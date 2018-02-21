{- |
This module provides a feasibility check using LARE.

More pricesly this module implements:

  * an abstraction from ITS to LARE, and
  * a wrapper for the LARE library.


TODO: MS:

   * loopstructure should use a greedy algorithm
     * not necessarily just maxing oriented rules but using disjunctive bounds
     * we have a lot of examples where nesting is unnecessarily generated
   * unfold the TG beforehand not during translation

-}
{-# LANGUAGE RecordWildCards, StandaloneDeriving #-}
module Tct.Its.Processor.Lare where

import           Control.Monad                    (when)
import           Data.Foldable                    (toList)
import qualified Data.IntMap.Strict               as IM
import           Data.List                        (intersperse)
import           Data.Monoid                      ((<>))
import qualified Data.Set                         as S

import           Tct.Core.Common.Pretty           (Pretty, pretty)
import qualified Tct.Core.Common.Pretty           as PP
import           Tct.Core.Common.Xml              (Xml, toXml)
import qualified Tct.Core.Common.Xml              as Xml
import qualified Tct.Core.Data                    as T

import qualified Tct.Common.Polynomial            as P

import           Tct.Its.Data.Complexity          (Complexity (..))
import qualified Tct.Its.Data.LocalSizebounds     as LB (Minimize (..), computeWith, lboundOf)
import           Tct.Its.Data.Problem
import qualified Tct.Its.Data.Timebounds          as TB (initialise)
import qualified Tct.Its.Data.TransitionGraph     as TG
import           Tct.Its.Data.Types
import qualified Tct.Its.Processor.Looptree       as LT

import qualified Lare.Analysis                    as LA
import qualified Lare.Flow                        as LA
import qualified Lare.Tick                        as LA


type Edge v l    = LA.Edge v (l (LA.Var Var))
data Program l = Program
  { dom :: [LA.Var Var]
  , cfg :: LA.Program Fun (l (LA.Var Var)) }
type Proof     = LA.Tree [Edge (LA.Vtx Fun) LA.F]
type SizeAbstraction = Program LA.Assignment
type FlowAbstraction = Program LA.F

deriving instance Show (Program LA.Assignment)
deriving instance Show (Program LA.F)

-- Size Abstraction of the ITS. Replaces constraints of each edge of the CFG with its local growh.
-- For example:
-- @l1(x,y,z) -> l2(x-1,y',z) :|: x > 0 && y' > 0 && y <= z@ is transformed to
-- @l1 -> l2 [x' <= x, y' <= z, z' <= z ]@
toEdges :: Its -> IM.IntMap (Edge Fun LA.Assignment)
toEdges prob = flip IM.mapWithKey (irules_ prob) $
  \i Rule{..} ->
    LA.edge
      (fun lhs)
      (LA.Assignment
        [ (LA.Var v, toBound $ LB.lboundOf lsb rv) | v <- domain prob, let rv = RV i 0 v ])
      (fun $ head rhs)
  where Just lsb = localSizebounds_ prob

toBound :: Complexity -> LA.Bound (LA.Var Var)
toBound Unknown   = LA.Unknown
toBound (NPoly p) = foldr k (LA.Sum []) (P.toView p) where
  k (c,[])      (LA.Sum bs) = LA.Sum $ (c, LA.K):bs
  k (c,[(v,i)]) (LA.Sum bs)
    | i == 1                = LA.Sum $ (c, LA.Var v):bs
  k _ _                     = LA.Unknown

data UseGraph = UseCFG | UseTG
  deriving (Eq, Ord, Show)

toEdges' :: Its -> UseGraph -> Int -> [Edge Fun LA.Assignment]

toEdges' prob UseCFG i = pure $
  LA.edge
    (fun lhs)
    (LA.Assignment
      [ (LA.Var v, toBound $ LB.lboundOf lsb rv) | v <- domain prob, let rv = RV i 0 v ])
    (fun $ head rhs)
  where
    Just lsb = localSizebounds_ prob
    Rule{..} = irules_ prob IM.! i

toEdges' prob UseTG i = do
  let 
    sucs1 = fst `fmap` TG.successors (tgraph_ prob) i
    sucs2 = if null sucs1 then i:sucs1 else sucs1
  suc <- sucs2
  return $
    LA.Edge
      (toF lhs i)
      (LA.Assignment
        [ (LA.Var v, toBound $ LB.lboundOf lsb rv) | v <- domain prob, let rv = RV i 0 v ])
      (toF (head . rhs) suc)
  where
    Just lsb = localSizebounds_ prob
    toF k n  = fun (k $ irules_ prob IM.! i) ++ "." ++ show n

-- Transforms the ITS and computed loop structure to the intermediate represenation of the LARE library.
toLare :: Its -> UseGraph -> LT.Top [RuleId] -> Program LA.Assignment
toLare prob usegraph lt =
  let
    lare = LA.toProgram $ go0 lt
    vs1  = [ LA.Var v | v <- domain prob ]
    vs2  = [ LA.Ann v | l <- toList lare, let LA.Assignment [ (LA.Ann v,_) ] = LA.loopid l ]
  in
  Program (vs1++vs2) lare

  where
  from  = concatMap (toEdges' prob usegraph)

  go0 (LT.Top es ts)    = LA.Top (from es) (goN `fmap` zip (positions [0]) ts)
  goN (pos,LT.Tree{..}) = LA.Tree (loop (from program) pos bound) (goN `fmap` zip (positions pos) subprograms)

  loop cfg' pos bnd = LA.SimpleLoop
    { LA.program' = cfg'
    , LA.loopid'  = LA.Assignment [(LA.Ann (posToVar pos), toBound bnd)] }
    where
      posToVar = intersperse '.' . concatMap show . reverse

  positions pos = (:pos) `fmap` iterate succ (0 :: Int)


toLareM :: Its -> UseGraph -> LB.Minimize -> LT.Top [RuleId] -> T.TctM (Program LA.Assignment)
toLareM prob usegraph minimize lt = do
  lbs <- LB.computeWith minimize (domain prob) (irules_ prob)
  let
    prob' = prob
      { localSizebounds_ = Just lbs
      , sizebounds_      = Nothing
      , rvgraph_         = Nothing }
  return $ toLare prob' usegraph lt


-- LARE requires start and exit nodes.
-- Analyse the SCC dependency tree and add sinks if necessary.
addSinks :: Its -> Its
addSinks prob = prob
  { irules_          = allrules
  , tgraph_          = TG.estimateGraph allrules
  , rvgraph_         = Nothing
  , timebounds_      =
      TB.initialise
        (IM.keys allrules)
        (IM.keys $ IM.filter (\r -> fun (lhs r) == fun (startterm_ prob) ) allrules)
  , sizebounds_      = Nothing
  , localSizebounds_ = Nothing }

  where
  allrules = irules `IM.union` sinks

  irules = irules_ prob
  term f = Term { fun = f, args = args (startterm_ prob) }
  rule f = Rule { lhs = term f, rhs = [ term "exitus616"], con = [] }

  sinks = IM.fromList $
    zip
     [ succ (fst (IM.findMax irules)) ..]
     [ rule f |  f <- nub [ fun (lhs r) | n <- needSinks, let r = irules IM.! n ] ]
  nub = S.toList . S.fromList

  needSinks =
    concat
      [ theSCC scc
        | ps <- TG.rootsPaths (tgraph_ prob)
        , let scc = last ps
        , isNonTrivial scc ]

  isNonTrivial (NonTrivial _) = True
  isNonTrivial _              = False




--- * Processors -----------------------------------------------------------------------------------------------------

data AddSinksProcessor = AddSinks deriving Show

instance T.Processor AddSinksProcessor where
  type ProofObject AddSinksProcessor = ()
  type In AddSinksProcessor          = Its
  type Out AddSinksProcessor         = Its
  type Forking AddSinksProcessor     = T.Id

  execute AddSinks prob = T.succeedWithId () (addSinks prob)


data LooptreeTransformer = LooptreeTransformer deriving Show

instance T.Processor LooptreeTransformer where
  type ProofObject LooptreeTransformer = LT.LooptreeProof
  type In LooptreeTransformer          = Its
  type Out LooptreeTransformer         = (Its, LT.LooptreeProof)
  type Forking LooptreeTransformer     = T.Id

  execute LooptreeTransformer prob = do
    tree <- LT.infer prob
    let proof = LT.LooptreeProof tree
    if LT.isComplete tree
      then T.succeedWithId proof (prob,proof)
      else T.abortWith proof


data SizeAbstractionProcessor = SizeAbstraction UseGraph LB.Minimize deriving Show

instance T.Processor SizeAbstractionProcessor where
  type ProofObject SizeAbstractionProcessor = ()
  type In SizeAbstractionProcessor          = (Its, LT.LooptreeProof)
  type Out SizeAbstractionProcessor         = SizeAbstraction
  type Forking SizeAbstractionProcessor     = T.Id

  execute (SizeAbstraction usegraph minimize) (prob, LT.LooptreeProof tree) = 
    T.succeedWithId () =<< toLareM prob usegraph minimize tree


data FlowAbstractionProcessor = FlowAbstraction deriving Show

instance T.Processor FlowAbstractionProcessor where
  type ProofObject FlowAbstractionProcessor = ()
  type In FlowAbstractionProcessor          = SizeAbstraction
  type Out FlowAbstractionProcessor         = FlowAbstraction
  type Forking FlowAbstractionProcessor     = T.Id

  execute FlowAbstraction (Program vs prob) = T.succeedWithId () $ Program vs' (LA.toFlow vs' prob)
    where vs' = LA.Counter: LA.Huge : LA.K : vs


data LareProcessor = LareProcessor deriving Show
data LareProof = LareProof Proof deriving Show

instance T.Processor LareProcessor where
  type ProofObject LareProcessor = LareProof
  type In LareProcessor          = FlowAbstraction
  type Out LareProcessor         = ()
  type Forking LareProcessor     = T.Judgement

  execute LareProcessor (Program vs prob) =
    let
      proofM = do
        -- proof <- LA.convertWith (LA.ticked $ LA.flow vs) prob
        proof <- Right $ LA.convert (LA.ticked $ LA.flow vs) prob
        let bound = LA.boundOfProof proof
        when (bound == LA.Indefinite) (Left "Unknown bound.")
        return (proof, bound)
    in
    either
      T.abortWith
      (\(proof, bound) -> T.succeedWith0 (LareProof proof) (T.judgement $ T.timeUBCert $ toComplexity bound))
      proofM


toComplexity :: LA.Complexity -> T.Complexity
toComplexity LA.Indefinite = T.Unknown
toComplexity LA.Constant   = T.Poly (Just 0)
toComplexity LA.Linear     = T.Poly (Just 1)
toComplexity LA.Polynomial = T.Poly Nothing
toComplexity LA.Primrec    = T.Primrec


--- * Pretty ---------------------------------------------------------------------------------------------------------

instance Xml.Xml (Its,LT.LooptreeProof) where toXml = const Xml.empty
instance Xml.Xml (a,Program l)          where toXml = const Xml.empty
instance Xml.Xml (Program l)            where toXml = const Xml.empty

instance Pretty LareProof where pretty (LareProof p) = pretty p
instance Xml LareProof where toXml = const Xml.empty

instance Pretty (Program LA.Assignment) where pretty = ppProgram pretty
instance Pretty (Program LA.F) where pretty = ppProgram pretty

ppProgram :: (LA.Program Fun (t (LA.Var Var)) -> PP.Doc) -> Program t -> PP.Doc
ppProgram k (Program vs p) = PP.vcat
  [ PP.text "Program:"
  , PP.indent 2 $ PP.text "Domain: " <> PP.pretty vs
  , PP.indent 2 $ PP.align $ k p ]

