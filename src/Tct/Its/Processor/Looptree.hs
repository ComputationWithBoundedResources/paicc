-- | This module tries to infer a \loop structure\ of an ITS.
-- Infers a lexicographric combination of linear ranking functions.
{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, LambdaCase #-}
module Tct.Its.Processor.Looptree where


import           Data.Either                         (partitionEithers)
import           Data.Function                       (on)
import qualified Data.IntMap.Strict                  as IM
import           Data.List                           ((\\))
import qualified Data.Map.Strict                     as M
import           Data.Maybe                          (catMaybes, fromMaybe)

import           Tct.Its.Data.Complexity             as C
import           Tct.Its.Data.Problem
import           Tct.Its.Data.Rule
import qualified Tct.Its.Data.Timebounds             as TB
import qualified Tct.Its.Data.TransitionGraph        as TG
import           Tct.Its.Data.Types
import qualified Tct.Its.Processor.PolyRank          as P
import qualified Tct.Its.Processor.Simplification    as S

import qualified Tct.Common.Polynomial               as Poly
import qualified Tct.Common.PolynomialInterpretation as PI
import           Tct.Common.Ring
import qualified Tct.Common.SMT                      as SMT

import           Tct.Core
import qualified Tct.Core.Common.Pretty              as PP
import qualified Tct.Core.Common.Xml                 as Xml
import qualified Tct.Core.Data                       as T


--- * processor ------------------------------------------------------------------------------------------------------

withSimpl :: Strategy Its o -> Strategy Its o
withSimpl st =
  try S.boundTrivialSCCs
  .>>> try S.unsatRules
  .>>> try S.unsatPaths
  .>>> try S.unreachableRules
  .>>> try S.leafRules
  .>>> st

data Simplify = Simplify | NoSimplify
  deriving (Eq, Show, Enum, Bounded)

simpArg :: T.Argument 'T.Required Simplify
simpArg = T.flag "simplify" ["Specifies whether to apply additional simplifications."]

cyclemania :: Declaration ('[Argument 'Optional Simplify] :-> Strategy Its Its)
cyclemania =
  T.declare
    "cyclemania"
    ["Tries to infer a linear polynomial ranking function for each cyclic path."]
    (OneTuple $ simpArg `optional` Simplify)
    (\case
       Simplify   -> withSimpl (processor CycleMania)
       NoSimplify -> processor CycleMania)

looptree :: Declaration ('[Argument 'Optional Simplify] :-> Strategy Its Its)
looptree =
  T.declare
    "looptree"
    ["Tries to construct a loop tree."]
    (OneTuple $ simpArg `optional` Simplify)
    (\case
       Simplify   -> withSimpl (processor Looptree)
       NoSimplify -> processor Looptree)

restrictToRuleIds :: [RuleId] -> Its -> Maybe Its
restrictToRuleIds []    _   = Nothing
restrictToRuleIds is its = Just
  Its
    { irules_          = rulex
    , signature_       = signature_ its
    , startterm_       = startterm_ its
    , tgraph_          = TG.estimateGraph rulex
    , rvgraph_         = Nothing
    , timebounds_      = TB.initialise (IM.keys rulex) [fresh]
    , sizebounds_      = Nothing
    , localSizebounds_ = Nothing }

  where
    fresh = head $ [0..] \\ is
    entry = Rule (startterm_ its) [lhs $ find (head is)] []
    rulex = IM.insert fresh entry  $ IM.filterWithKey (\k _ -> k `elem` is) (irules_ its)
    find k = fromMaybe (error $ "restrictToRuleIds.not found: " ++ show k) (IM.lookup k rulex)


--- * cyclemania -----------------------------------------------------------------------------------------------------
-- this processor computes all simple cyclic paths and tries to infer a (linear) polynomial ranking function for each
-- one;
-- this processor intended for testing only: informally if this processor fails then a complexity analysis relying on
-- linear prfs only (shold) fail


data CycleManiaProcessor = CycleMania
  deriving Show

type Proof = Either Its (Its,P.PolyOrder)

data CycleManiaProof = CycleManiaProof [Proof]
  deriving Show

instance T.Processor CycleManiaProcessor where
  type ProofObject CycleManiaProcessor = CycleManiaProof
  type In CycleManiaProcessor          = Its
  type Out CycleManiaProcessor         = Its
  type Forking CycleManiaProcessor     = T.Judgement

  execute CycleMania prob = do
    let probs = catMaybes $ flip restrictToRuleIds prob `fmap` TG.simpleCycles (irules_ prob)
    proofs <- mapM entscheide probs
    let certfn = const $ T.yesNoCert $all (either (const False) (const True)) proofs
    T.succeedWith0 (CycleManiaProof proofs) certfn

farkas :: P.PolyRankProcessor
farkas = P.polyRankProcessor { P.useFarkas = True, P.shape = PI.Linear }

entscheide :: Its -> T.TctM Proof
entscheide its = do
  result <- P.entscheide farkas its
  return $ case result of
    SMT.Sat order   -> Right (its,order)
    _               -> Left its


--- * looptree -------------------------------------------------------------------------------------------------------
--
-- A. M. Ben-Amram and A. Pineles, "Flowchart Programs, Regular Expressions, and Decidability of Polynomial
-- Growth-Rate.", VPT@ETAPS, 2016

data Top a = Top a [Tree a]
  deriving (Show, Functor, Foldable, Traversable)

data Tree a
  = Tree
  { program     :: a
  , cutset      :: a
  , bound       :: Complexity
  , subprograms :: [Tree a] }
  deriving (Show, Functor, Foldable, Traversable)

draw :: Show a => Top a -> [String]
draw (Top p ts0) = ("P: " ++ show p)  : drawSubTrees ts0 where
  draw' t@Tree{} = ("p:" ++ show (program t) ++ " c: " ++ show (cutset t))  : drawSubTrees (subprograms t)
  shift first other = zipWith (++) (first : repeat other)
  drawSubTrees []     = []
  drawSubTrees [t]    = "|" : shift "`- " "   " (draw' t)
  drawSubTrees (t:ts) = "|" : shift "+- " "|  " (draw' t) ++ drawSubTrees ts

isComplete :: Top [RuleId] -> Bool
isComplete (Top _ ts0)      = all isComplete' ts0 where
  isComplete' (Tree [] [] _ []) = True
  isComplete' (Tree _  cs _ ts)
    | null ts   = not (null cs)
    | otherwise = all isComplete' ts

data LooptreeProcessor = Looptree
  deriving Show

data LooptreeProof = LooptreeProof (Top [RuleId])
  deriving Show

instance T.Processor LooptreeProcessor where
  type ProofObject LooptreeProcessor = LooptreeProof
  type In LooptreeProcessor          = Its
  type Out LooptreeProcessor         = Its
  type Forking LooptreeProcessor     = T.Judgement

  execute Looptree prob = do
    tree <- infer prob
    T.succeedWith0 (LooptreeProof tree) (const $ T.yesNoCert $ isComplete tree)


infer :: Its -> T.TctM (Top [RuleId])
infer prob = go0 (IM.keys $ irules_ prob) where
  go0 rs = Top rs <$> sequence [ goN ns | ns <- TG.nonTrivialSCCs (tgraph_ prob) ]
  goN [] = return $ Tree [] [] one []
  goN rs = do
    let Just its = restrictToRuleIds rs prob
    result <- P.entscheide farkas its
    case result of
      SMT.Sat order ->
        let
          is      = [ i | (i,_,_,_) <- P.strict_ order ]
          tgraph' = TG.deleteNodes is $ TG.restrictToNodes rs $ tgraph_ prob
        in
        Tree rs is (boundOf prob order) <$> sequence [ goN ns | ns <- TG.nonTrivialSCCs tgraph' ]
      _             ->
        return $ Tree rs [] C.Unknown []

boundOf :: Its -> P.PolyOrder -> Complexity
boundOf prob order = C.poly $ normalize [ interpret int | int <- M.elems (PI.interpretations $ P.pint_ order) ] where
  interpret int = Poly.substituteVariables int $ M.fromList $ zip PI.indeterminates (args $ startterm_ prob)
  normalize     = foldr (Poly.zipCoefficientsWith (max `on` abs)) (Poly.fromView [])


--- * pretty print ---------------------------------------------------------------------------------------------------

instance PP.Pretty LooptreeProof where
  pretty (LooptreeProof t)= PP.vcat
    [ PP.text "We construct a looptree:"
    , PP.indent 2 $ PP.vcat $ PP.text <$> draw t ]

instance Xml.Xml LooptreeProof where
  toXml = Xml.text . show

instance PP.Pretty CycleManiaProof where
  pretty (CycleManiaProof proofs) = PP.vcat
    [ PP.text "We rank cyclic paths:"
    , PP.text "Solved Problems:"
    , PP.indent 2 $ PP.itemise (PP.char '-') $ flip map solved $ \(its,order) ->
      PP.vcat
       [ PP.text "Problem:"
       , PP.indent 2 $ PP.pretty its
       , PP.text "Rank:"
       , PP.indent 2 $ PP.pretty order ]
    , PP.text "Open Problems:"
    , PP.indent 2 $ PP.itemise' (PP.char '-') open
    ]
    where
    (open, solved) = partitionEithers proofs

instance Xml.Xml CycleManiaProof where
  toXml = Xml.text . show

