-- | This module provides /size/ and /flow/ abstractions for CFG programs.
{-# LANGUAGE RecordWildCards, StandaloneDeriving #-}
module Tct.Paicc.Abstraction where


import           Data.Foldable                (toList)
import qualified Data.IntMap.Strict           as IM
import           Data.List                    (intersperse)
import           Data.Monoid                  ((<>))

import           Tct.Core.Common.Pretty       (Pretty, pretty)
import qualified Tct.Core.Common.Pretty       as PP
import qualified Tct.Core.Data                as T

import qualified Tct.Common.Polynomial        as P

import           Tct.Its.Data.Complexity      (Complexity (..))
import           Tct.Its.Data.LocalSizebounds (LocalSizebounds)
import qualified Tct.Its.Data.LocalSizebounds as LB (Minimize (..), computeWith, lboundOf)

import qualified Lare.Analysis                as LA
import qualified Lare.Flow                    as LA
import qualified Lare.Tick                    as LA

import           Tct.Paicc.Decomposition      as LT (LoopStructure (..), Tree (..))
import           Tct.Paicc.Problem


type Edge v l    = LA.Edge v (l (LA.Var Var))
data Program l = Program
  { dom :: [LA.Var Var]
  , cfg :: LA.Program Fun (l (LA.Var Var)) }
type Proof     = LA.Tree [Edge (LA.Vtx Fun) LA.F]
type SizeAbstraction = Program LA.Assignment
type FlowAbstraction = Program LA.F

deriving instance Show SizeAbstraction
deriving instance Show FlowAbstraction


-- * Size Abstraction

-- MS: v0.2
-- The local-growth abstraction is not unique (even with minimisation). Sometimes the obtained results are not optimal
-- because the "wrong" abstractions is inferred. A possible easy extension to 'Lare' could be to consider (bounded)
-- set of flows and generate for each edge multiple candidates.

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

toLare :: Paicc -> LocalSizebounds -> LT.LoopStructure [RuleId] -> SizeAbstraction
toLare prob lsb lt =
  let
    lare = LA.toProgram $ go0 lt
    vs1  = [ LA.Var v | v <- domain_ prob ]
    vs2  = [ LA.Ann v | l <- toList lare, let LA.Assignment [ (LA.Ann v,_) ] = LA.loopid l ]
  in
  Program (vs1++vs2) lare

  where
  lbs = toEdges prob lsb
  from = fmap (lbs IM.!)

  go0 (LT.Top es ts)    = LA.Top (from es) (goN `fmap` zip (positions [0]) ts)
  goN (pos,LT.Tree{..}) = LA.Tree (loop (from program) pos bound) (goN `fmap` zip (positions pos) subprograms)

  loop cfg' pos bnd = LA.SimpleLoop
    { LA.program' = cfg'
    , LA.loopid'  = LA.Assignment [(LA.Ann (posToVar pos), toBound bnd)] }
    where
      posToVar = intersperse '.' . concatMap show . reverse

  positions pos = (:pos) `fmap` iterate succ (0 :: Int)


toLareM :: Paicc -> LB.Minimize -> LT.LoopStructure [RuleId] -> T.TctM SizeAbstraction
toLareM prob minimize lt = do
  lsb <- LB.computeWith minimize (domain_ prob) (irules_ prob)
  return $ toLare prob lsb lt


-- * Flow Abstraction ('Tick' Domain)

toFlow :: SizeAbstraction -> FlowAbstraction
toFlow Program{..} = Program{dom = dom', cfg = LA.toFlow dom' cfg}
  where dom' =  LA.Counter: LA.Huge : LA.K : dom


-- * Pretty Printing

instance Pretty SizeAbstraction where pretty = ppProgram pretty
instance Pretty FlowAbstraction where pretty = ppProgram pretty

ppProgram :: (LA.Program Fun (t (LA.Var Var)) -> PP.Doc) -> Program t -> PP.Doc
ppProgram k (Program vs p) = PP.vcat
  [ PP.text "Program:"
  , PP.indent 2 $ PP.text "Domain: " <> PP.pretty vs
  , PP.indent 2 $ PP.align $ k p ]

