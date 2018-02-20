{-# LANGUAGE MultiParamTypeClasses #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures -fno-warn-orphans #-}
module Main (main) where

import           Tct.Core
import qualified Tct.Core.Data                as T
import           Tct.Core.Main                (AnswerFormat (..))

import           Tct.Its                      hiding (mixed)
import           Tct.Its.Data.LocalSizebounds (Minimize (..))
import           Tct.Its.Data.Types           (args)
import           Tct.Its.Processor.Lare
import           Tct.Its.Processor.Looptree   (LooptreeProcessor (..))
import qualified Tct.Its.Strategies           as S

instance Declared Its Its where
  decls =
    [ SD $ T.strategy "loopstructure"   () loopstructure
    , SD $ T.strategy "flowAbstraction" () flowAbstraction
    , SD $ T.strategy "lare"            () lare
    , SD $ T.strategy "mixed"           () $ withArgumentFilter mixed
    , SD $ T.strategy "pervasive"       () $ withArgumentFilter pervasive ]

main :: IO ()
main = runIts $
  itsConfig
    { defaultStrategy = mixed
    , putAnswer       = Left TTTACAnswerFormat }

withSimpl st =
  try boundTrivialSCCs
  .>>> try unsatRules
  .>>> try unsatPaths
  .>>> try unreachableRules
  .>>> st

loopstructure = withSimpl $ T.processor Looptree

flowAbstraction = withSimpl $
  processor AddSinks
  .>>> try S.unsatPaths
  .>>> processor LooptreeTransformer
  .>>> processor (SizeAbstraction UseCFG Minimize)
  .>>> processor FlowAbstraction
  .>>> close

lare = withSimpl $
  processor AddSinks
  .>>> try S.unsatPaths
  .>>> processor LooptreeTransformer
  .>>> processor (SizeAbstraction UseCFG Minimize)
  .>>> processor FlowAbstraction
  .>>> processor LareProcessor
  .>>> close

rank = withSimpl $
  te (farkas .>>> try knowledgePropagation)
  .>>> close

mixed = rank .<|> lare

lareN = withSimpl $
  processor AddSinks
  .>>> try S.unsatPaths
  .>>> processor LooptreeTransformer
  .>>> best cmpTimeUB [ timeoutRemaining (flow u m) | u <- [UseCFG, UseTG], m <- [Minimize, NoMinimize] ]
  .>>> processor FlowAbstraction
  .>>> processor LareProcessor
  .>>> close
  where
    flow u m = 
      processor (SizeAbstraction u m) 
      .>>> processor FlowAbstraction
      .>>> processor LareProcessor
      .>>> close

pervasive = rank .<|> lareN

withArgumentFilter st = try (withProblem af) .>>> st
  where af p = when (length (args $ startterm_ p) > 12) (argumentFilter (unusedFilter p))

