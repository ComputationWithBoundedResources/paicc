-- | This module tries to infer a \loop structure\ of an ITS.
-- Infers a lexicographric combination of linear ranking functions.
{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, FlexibleContexts, ScopedTypeVariables #-}
module Tct.Paicc.LoopStructure where


import           Data.Function                       (on)
import qualified Data.IntMap.Strict                  as IM
import qualified Data.Map.Strict                     as M
import           Data.Maybe                          (fromMaybe)
import           Data.Monoid                         ((<>))

import           Tct.Its.Data.Complexity             (Complexity)
import qualified Tct.Its.Data.Complexity             as C (Complexity (..), poly)
import           Tct.Its.Data.Rule                   (AAtom (..), filterLinear, interpretTerm, toGte)
import qualified Tct.Its.Data.TransitionGraph        as TG

import qualified Tct.Common.Polynomial               as P
import qualified Tct.Common.PolynomialInterpretation as PI
import           Tct.Common.Ring
import           Tct.Common.SMT                      ((.&&), (.==), (.=>), (.>), (.>=))
import qualified Tct.Common.SMT                      as SMT

import qualified Tct.Core.Data                       as T

import           Lare.Util                           ((\\))

import           Tct.Paicc.Problem


data Top a = Top a [Tree a]
  deriving (Show, Functor, Foldable, Traversable)

data Tree a
  = Tree
  { program     :: a
  , cutset      :: a
  , bound       :: Complexity
  , subprograms :: [Tree a] }
  deriving (Show, Functor, Foldable, Traversable)

isComplete :: Top [RuleId] -> Bool
isComplete (Top _ ts0)      = all isComplete' ts0 where
  isComplete' (Tree [] [] _ []) = True
  isComplete' (Tree _  cs _ ts)
    | null ts   = not (null cs)
    | otherwise = all isComplete' ts

restrict :: [RuleId] -> Paicc -> Paicc
restrict irs prob = prob
  { irules_ = IM.filterWithKey (\k _ -> k `elem` irs) (irules_ prob)
  , tgraph_ = TG.restrictToNodes irs (tgraph_ prob) }

findM :: (Ord k, Show k) => M.Map k a -> k -> a
findM m k = error err `fromMaybe` M.lookup k m
  where err = "Tct.Paicc.LoopStructure: key " ++ show k ++ " not found."

findIM :: IM.IntMap a -> Int -> a
findIM m k = error err `fromMaybe` IM.lookup k m
  where err = "Tct.Paicc.LoopStructure: key " ++ show k ++ " not found."

type Encoding = (PI.PolyInter Fun (SMT.IExpr Int), IM.IntMap (SMT.IExpr Int))
type Decoding = (PI.PolyInter Fun Int, IM.IntMap Int)

-- provides an encoding for linear ranking function 
orientation :: Rules -> Signature -> SMT.SolverSt (SMT.SmtState Int) Encoding
orientation irules signature = do
  SMT.setLogic SMT.QF_LIA

  aint <- PI.PolyInter <$> traverse encode signature
  bnds <- traverse (const SMT.nvarM') irules

  let
    strict = findIM bnds
    interpretLhs    = interpret aint
    interpretRhs ts = interpret aint (head ts)
    interpretCon cs = [ P.mapCoefficients SMT.num c | Gte c _ <- toGte cs ]

  let
    decreasing (i,Rule l rs cs) = pl `eliminate` interpretCon (filterLinear cs)
      where pl = interpretLhs l `sub` (interpretRhs rs `add` P.constant (strict i))
    bounded (Rule l _ cs) = (interpretLhs l) `eliminate` interpretCon (filterLinear cs)

    absolute p = SMT.bigAnd [ c .== SMT.zero | c <- P.coefficients p ]
    eliminate ply cs = do
      let
        k p = SMT.nvarM' >>= \lambda -> return (lambda `P.scale` p)
      cs2 <- mapM k cs
      let
        (p1,pc1) = P.splitConstantValue ply
        (p2,pc2) = P.splitConstantValue (bigAdd cs2)
      return $ absolute (p1 `sub` p2) .&& (pc1 .>= pc2)

  let
    order (i,r) = do
      fm1 <- decreasing (i,r)
      fm2 <- bounded r
      return (fm1 .&& (strict i .> SMT.zero .=> fm2))


  SMT.assert (SMT.top :: SMT.Formula Int)
  SMT.assert =<< SMT.bigAndM [ order r | r <- IM.assocs irules ]

  return (aint, bnds)

  where

  encode ar = P.fromViewWithM (const SMT.ivarM') (linear ar)
  linear ar = P.linear (const ()) (take ar PI.indeterminates)

  interpret aint = interpretTerm interpretFun interpretArg where
    interpretFun f = P.substituteVariables (PI.interpretations aint `findM` f) . M.fromList . zip PI.indeterminates
    interpretArg   = P.mapCoefficients SMT.num

data Order = Order
  { strict_ :: [Int]
  , bound_  :: Complexity }
  deriving Show

instance Monoid Order where
  mempty        = Order { strict_ = [], bound_ = zero }
  mappend o1 o2 = Order { strict_ = strict_ o1 <> strict_ o2, bound_ = bound_ o1 `add` bound_ o2 }

update :: Paicc -> Paicc -> Decoding -> Order -> Order
update prob sprob (pint,stricts) old = old <> Order { strict_ = strict' , bound_ = bound' } where
  strict' = IM.keys $ IM.filter (>0) stricts
  fs      = (fun . head . rhs . findIM (irules_ prob) . fst) `fmap` TG.incoming (tgraph_ prob) (IM.keys $ irules_ sprob)
  bound'  = boundOf fs (domain_ prob) pint

boundOf :: [Fun] -> [Var] -> PI.PolyInter Fun Int -> Complexity
boundOf fs vs pint = C.poly $ normalize [ interpret int | (f,int) <- M.assocs (PI.interpretations pint), f `elem` fs ]
  where
  interpret int = P.substituteVariables int $ M.fromList $ zip PI.indeterminates [ P.variable v | v <- vs ]
  normalize     = foldr (P.zipCoefficientsWith (max `on` abs)) zero

data Greedy = Greedy | NoGreedy
  deriving (Eq, Ord, Show, Enum, Bounded)

farkas :: Paicc -> Paicc -> Greedy -> T.TctM Order
farkas prob sprob NoGreedy = do
  let encodingSMT = flip SMT.runSolverSt SMT.initialState $ orientation (irules_ sprob) (signature_ sprob)
  either id id <$> farkasN prob sprob encodingSMT mempty
farkas prob sprob Greedy = do
  let encodingSMT = flip SMT.runSolverSt SMT.initialState $ orientation (irules_ sprob) (signature_ sprob)
  go mempty encodingSMT
  where
    go order smt = do
      res <- farkasN prob sprob smt order
      case res of
        Left  new -> go new smt
        Right new -> pure new

farkasN :: Paicc -> Paicc -> (Encoding, SMT.SmtState Int) -> Order -> T.TctM (Either Order Order)
farkasN prob sprob (encoding, st) order
  | null todo = pure $ Right order
  | otherwise = do
  res :: SMT.Result Decoding <- SMT.solveSt SMT.yices st $ do
    SMT.assert $ SMT.bigOr [ snd encoding `findIM` i .> zero | i <- todo ]
    pure $ SMT.decode encoding
  pure $ case res of
    SMT.Sat decoding -> Left $ update prob sprob decoding order
    _                -> Right order
  where todo = IM.keys (irules_ sprob) \\ strict_ order

infer :: Paicc -> T.TctM (Top [RuleId])
infer = inferWith Greedy

inferWith :: Greedy -> Paicc -> T.TctM (Top [RuleId])
inferWith greedy prob = go0 (IM.keys $ irules_ prob) where
  go0 rs = Top rs <$> sequence [ goN ns | ns <- TG.nonTrivialSCCs (tgraph_ prob) ]
  goN [] = return $ Tree [] [] one []
  goN rs = do
    let sprob = restrict rs prob
    order <- farkas prob sprob greedy
    if null (strict_ order)
      then return $ Tree rs [] C.Unknown []
      else
        let
          tgraph' = TG.deleteNodes (strict_ order) $ (tgraph_ sprob)
        in
        Tree rs (strict_ order) (bound_ order) <$> sequence [ goN ns | ns <- TG.nonTrivialSCCs tgraph' ]


-- * Pretty Print

draw :: Show a => Top a -> [String]
draw (Top p ts0) = ("P: " ++ show p)  : drawSubTrees ts0 where
  draw' t@Tree{} = ("p:" ++ show (program t) ++ " c: " ++ show (cutset t))  : drawSubTrees (subprograms t)
  shift first other = zipWith (++) (first : repeat other)
  drawSubTrees []     = []
  drawSubTrees [t]    = "|" : shift "`- " "   " (draw' t)
  drawSubTrees (t:ts) = "|" : shift "+- " "|  " (draw' t) ++ drawSubTrees ts

