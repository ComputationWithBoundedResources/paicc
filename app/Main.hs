{-# LANGUAGE MultiParamTypeClasses #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures -fno-warn-orphans #-}
module Main (main) where

import Tct.Core
import Tct.Core.Main      (AnswerFormat (..))

import Tct.Its
import Tct.Its.Data.Types (args)

import Tct.Paicc


instance Declared Its Its where
  decls =
    [ SD $ strategy "simple-greedy" ()    $ withArgumentFilter $ simple Unfold Greedy  Minimize
    , SD $ strategy "simple-no-greedy" () $ withArgumentFilter $ simple Unfold NoGreedy Minimize
    , SD $ strategy "hard" () $ withArgumentFilter hard
    , SD $ strategy "more" () $ more Greedy ]


main :: IO ()
main = runIts $
  itsConfig
    { defaultStrategy = simple NoUnfold Greedy Minimize
    , putAnswer       = Left TTTACAnswerFormat }


data Unfold = Unfold | NoUnfold 
  deriving (Eq, Ord, Show, Enum, Bounded)

withSimpl st =
  try unsatRules
  .>>> try unreachableRules
  .>>> st

withArgumentFilter st = try (withProblem af) .>>> st
  where af p = when (length (args $ startterm_ p) > 12) (argumentFilter (unusedFilter p))

rank =
  try boundTrivialSCCs
  .>>> te (farkas .>>> try knowledgePropagation)
  .>>> close

simple u g m = withSimpl $
  identity
  .>>> fromIts
  .>>> when (u == Unfold) unfold
  .>>> addSinks
  .>>> decompose g
  .>>> abstractSize m
  .>>> abstractFlow
  .>>> analyse
  .>>> close


goal sts = best cmpTimeUB [ timeoutRemaining st | st <- sts ]

prep = (unsatPaths .>>> fromIts .>>> unfold) .<|> (fromIts)

more greedy =
  withArgumentFilter $ withSimpl $ fastest [rank, lare] where
  lare =
    identity
    .>>> prep
    .>>> addSinks
    .>>> decompose greedy
    .>>> goal [ flow Minimize .>>> close, flow NoMinimize .>>> close ]
  flow :: Minimize -> Strategy Decomposition Its
  flow minimize =
    identity
    .>>> abstractSize minimize
    .>>> abstractFlow
    .>>> analyse
    .>>> close

hard = goal $ rank : [ simple u g m | u <- [Unfold, NoUnfold], g <- [Greedy, NoGreedy], m <- [Minimize, NoMinimize] ]


