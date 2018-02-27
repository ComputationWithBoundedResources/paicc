-- | This module provides \unfolding\ of the rulegraph representation to the nodegraph representation.
module Tct.Paicc.Unfold where

import qualified Data.IntMap.Strict           as IM
import qualified Data.Map.Strict              as M

import qualified Tct.Its.Data.TransitionGraph as TG

import           Tct.Paicc.Problem


unfold :: Paicc -> Paicc
unfold prob = Paicc
  { irules_    = allrules
  , tgraph_    = TG.estimateGraph allrules
  , domain_    = domain_ prob
  , signature_ = M.fromList [ (f,ar) | let ar = length (domain_ prob), f <- funs allrules ] }
  where
  allrules = IM.fromAscList $ zip [0..] (toRulesN prob)
  funs     = foldr (\r acc -> fun (lhs r) : map fun (rhs r) ++ acc) []

toRulesN :: Paicc -> [Rule]
toRulesN prob = concatMap (toRules1 (tgraph_ prob) (newkey prob)) (IM.assocs $ irules_ prob)
  where newkey = succ . fst . IM.findMax . irules_

toRules1 :: TGraph -> Int -> (RuleId, Rule) -> [Rule]
toRules1 tgraph newkey (i,rule) =
  let
    sucs1 = fst `fmap` TG.successors tgraph i
    sucs2 = if null sucs1 then newkey:sucs1 else sucs1
  in
  [ rule{ lhs = lhs', rhs = rhs'   }
    | let lhs' = modFun (++ "." ++ show i) (lhs rule)
    , suc <- sucs2
    , let rhs' = modFun (++ "." ++ show suc) <$> rhs rule ]
  where
  modFun k a = a{ fun = k (fun a) }

