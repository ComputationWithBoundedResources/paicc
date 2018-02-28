{-# LANGUAGE RecordWildCards, StandaloneDeriving #-}
module Tct.Paicc.Abstraction where

import           Data.Foldable                    (toList)
import qualified Data.IntMap.Strict               as IM
import           Data.List                        (intersperse)
import           Data.Monoid                      ((<>))

import           Tct.Core.Common.Pretty           (Pretty, pretty)
import qualified Tct.Core.Common.Pretty           as PP
import qualified Tct.Core.Data                    as T

import qualified Tct.Common.Polynomial            as P

import           Tct.Its.Data.Complexity          (Complexity (..))
import           Tct.Its.Data.LocalSizebounds     (LocalSizebounds)
import qualified Tct.Its.Data.LocalSizebounds     as LB (Minimize (..), computeWith, lboundOf)
-- import           Tct.Its.Data.Problem
import qualified Tct.Its.Data.TransitionGraph     as TG
import           Tct.Its.Data.Types
-- import qualified Tct.Its.Processor.Looptree       as LT

import qualified Lare.Analysis                    as LA
import qualified Lare.Flow                        as LA
import qualified Lare.Tick                        as LA

import Tct.Paicc.Problem
import Tct.Paicc.Decomposition as LT (Top(..),Tree(..))

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
toEdges :: Paicc -> LocalSizebounds -> IM.IntMap (Edge Fun LA.Assignment)
toEdges prob lsb = flip IM.mapWithKey (irules_ prob) $
  \i Rule{..} ->
    LA.edge
      (fun lhs)
      (LA.Assignment
        [ (LA.Var v, toBound $ LB.lboundOf lsb rv) | v <- domain_ prob, let rv = RV i 0 v ])
      (fun $ head rhs)

toBound :: Complexity -> LA.Bound (LA.Var Var)
toBound Unknown   = LA.Unknown
toBound (NPoly p) = foldr k (LA.Sum []) (P.toView p) where
  k (c,[])      (LA.Sum bs) = LA.Sum $ (c, LA.K):bs
  k (c,[(v,i)]) (LA.Sum bs)
    | i == 1                = LA.Sum $ (c, LA.Var v):bs
  k _ _                     = LA.Unknown

data UseGraph = UseCFG | UseTG
  deriving (Eq, Ord, Show)

toEdges' :: Paicc -> LocalSizebounds -> UseGraph -> Int -> [Edge Fun LA.Assignment]

toEdges' prob lsb UseCFG i = pure $
  LA.edge
    (fun lhs)
    (LA.Assignment
      [ (LA.Var v, toBound $ LB.lboundOf lsb rv) | v <- domain_ prob, let rv = RV i 0 v ])
    (fun $ head rhs)
  where
    Rule{..} = irules_ prob IM.! i

toEdges' prob lsb UseTG i = do
  let 
    sucs1 = fst `fmap` TG.successors (tgraph_ prob) i
    sucs2 = if null sucs1 then i:sucs1 else sucs1
  suc <- sucs2
  return $
    LA.Edge
      (toF lhs i)
      (LA.Assignment
        [ (LA.Var v, toBound $ LB.lboundOf lsb rv) | v <- domain_ prob, let rv = RV i 0 v ])
      (toF (head . rhs) suc)
  where
    toF k n  = fun (k $ irules_ prob IM.! i) ++ "." ++ show n

toLare :: Paicc -> LocalSizebounds -> UseGraph -> LT.Top [RuleId] -> Program LA.Assignment
toLare prob lsb usegraph lt =
  let
    lare = LA.toProgram $ go0 lt
    vs1  = [ LA.Var v | v <- domain_ prob ]
    vs2  = [ LA.Ann v | l <- toList lare, let LA.Assignment [ (LA.Ann v,_) ] = LA.loopid l ]
  in
  Program (vs1++vs2) lare

  where
  from  = concatMap (toEdges' prob lsb usegraph)

  go0 (LT.Top es ts)    = LA.Top (from es) (goN `fmap` zip (positions [0]) ts)
  goN (pos,LT.Tree{..}) = LA.Tree (loop (from program) pos bound) (goN `fmap` zip (positions pos) subprograms)

  loop cfg' pos bnd = LA.SimpleLoop
    { LA.program' = cfg'
    , LA.loopid'  = LA.Assignment [(LA.Ann (posToVar pos), toBound bnd)] }
    where
      posToVar = intersperse '.' . concatMap show . reverse

  positions pos = (:pos) `fmap` iterate succ (0 :: Int)


toLareM :: Paicc -> UseGraph -> LB.Minimize -> LT.Top [RuleId] -> T.TctM (Program LA.Assignment)
toLareM prob usegraph minimize lt = do
  lsb <- LB.computeWith minimize (domain_ prob) (irules_ prob)
  return $ toLare prob lsb usegraph lt






-- --- * Pretty ---------------------------------------------------------------------------------------------------------

-- instance Xml.Xml (Its,LT.LooptreeProof) where toXml = const Xml.empty
-- instance Xml.Xml (a,Program l)          where toXml = const Xml.empty
-- instance Xml.Xml (Program l)            where toXml = const Xml.empty

-- instance Pretty LareProof where pretty (LareProof p) = pretty p
-- instance Xml LareProof where toXml = const Xml.empty

instance Pretty (Program LA.Assignment) where pretty = ppProgram pretty
instance Pretty (Program LA.F) where pretty = ppProgram pretty

ppProgram :: (LA.Program Fun (t (LA.Var Var)) -> PP.Doc) -> Program t -> PP.Doc
ppProgram k (Program vs p) = PP.vcat
  [ PP.text "Program:"
  , PP.indent 2 $ PP.text "Domain: " <> PP.pretty vs
  , PP.indent 2 $ PP.align $ k p ]

