-- | This module provides \unfolding\ of the rulegraph representation to the nodegraph representation.
module Tct.Paicc.Preprocessor where

import qualified Data.IntMap.Strict           as IM
import qualified Data.Map.Strict              as M

import qualified Tct.Its.Data.TransitionGraph as TG
import           Tct.Its.Data.Types           (theSCC)

import qualified Tct.Common.Polynomial as P (variable)

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




addSinks :: Paicc -> Paicc
addSinks prob = Paicc
  { irules_    = irules `IM.union` IM.fromList rules
  , tgraph_    = TG.insertEdges edges (tgraph_ prob)
  , signature_ = M.insert (fun exit) (length $ args exit) (signature_ prob)
  , domain_    = domain_ prob }
  where
  rules = [ (dst,rule over) | (_,over,dst) <- sinks ]
  edges = [ (src,dst,1) | (src,_,dst) <- sinks ]

  irules = irules_ prob
  term f = Term { fun = f, args = [ P.variable v | v <- domain_ prob] }
  exit   = term "exitus616"
  rule f = Rule { lhs = term f, rhs = [ exit ], con = [] }

  sinks =
    zipWith (\(src,over) dst -> (src,over,dst))
      [ (n,f) | n <- needSinks, let r = irules IM.! n, let f = fun (head $ rhs r) ]
      [ succ (fst $ IM.findMax irules) .. ]
  needSinks =
    concat [ theSCC scc | ps <- TG.rootsPaths (tgraph_ prob), let scc = last ps ]

