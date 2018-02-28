{-# LANGUAGE MultiParamTypeClasses #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures -fno-warn-orphans #-}
module Main (main) where

import           Tct.Core
import           Tct.Core.Main      (AnswerFormat (..))

import           Tct.Its
import           Tct.Its.Data.Types (args)

import           Tct.Paicc

instance Declared Its Its where
  decls =
    [ SD $ strategy "simple-greedy" ()    $ withArgumentFilter $ simple Greedy Minimize
    , SD $ strategy "simple-no-greedy" () $ withArgumentFilter $ simple NoGreedy Minimize ]

main :: IO ()
main = runIts $
  itsConfig
    { defaultStrategy = simple Greedy Minimize
    , putAnswer       = Left TTTACAnswerFormat }

withSimpl st =
  try unsatRules
  .>>> try unsatPaths
  .>>> try unreachableRules
  .>>> st

withArgumentFilter st = try (withProblem af) .>>> st
  where af p = when (length (args $ startterm_ p) > 12) (argumentFilter (unusedFilter p))

simple greedy minimize = withSimpl $
  identity
  .>>> fromIts
  .>>> unfold
  .>>> addSinks
  .>>> decompose greedy
  .>>> abstractSize minimize
  .>>> abstractFlow
  .>>> analyse
  .>>> close

