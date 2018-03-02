{-# LANGUAGE MultiParamTypeClasses, TypeFamilies #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures -fno-warn-orphans #-}
module Main (main) where

import           Tct.Core
import qualified Tct.Core.Data             as T
import           Tct.Core.Data.Certificate (yesNoCert)
import           Tct.Core.Main             (AnswerFormat (..))

import           Tct.Its
import           Tct.Its.Data.Types        (args)

import           Tct.Paicc


instance Declared Its Its where
  decls =
    [ SD $ strategy "loopstructure"  () $ loopstructure
    , SD $ strategy "simple"         () $ simple Slice NoUnfold Greedy Minimize
    , SD $ strategy "strategic"      () $ strategic Greedy Minimize
    , SD $ strategy "unlimited"      () $ unlimited ]

main :: IO ()
main = runIts $
  itsConfig
    { defaultStrategy = simple Slice NoUnfold Greedy Minimize
    , putAnswer       = Left TTTACAnswerFormat }


data Unfold = Unfold | NoUnfold
  deriving (Eq, Ord, Show, Enum, Bounded)

data Slice = Slice | NoSlice
  deriving (Eq, Ord, Show, Enum, Bounded)

sliceWhen k = withProblem $ \p -> when (k p) $ try $ argumentFilter (unusedFilter p)

rank =
  try knowledgePropagation
  .>>> te (farkas .>>> try knowledgePropagation)
  .>>> close

loopstructure =
  try unsatRules
  .>>> try unsatPaths
  .>>> try unreachableRules
  .>>> fromIts
  .>>> decompose'
  .>>> close
  .>>> best cmp
    [ timeoutRemaining $             decompose'
    , timeoutRemaining $ unfold .>>> decompose' ]
  where
  cmp t1 t2 = compare (T.outcome $ T.certificate t1) (T.outcome $ T.certificate t2)
  decompose' = ((decompose NoGreedy .>>> yes) .<|> no)
  yes = T.processor (CloseWith True)  :: T.Strategy Decomposition Its
  no  = T.processor (CloseWith False) :: T.Strategy Paicc Its

data CloseWith i o = CloseWith Bool deriving Show

instance (ProofData i, Show o) => T.Processor (CloseWith i o) where
  type ProofObject (CloseWith i o) = ()
  type In          (CloseWith i o) = i
  type Out         (CloseWith i o) = o
  type Forking     (CloseWith i o) = T.Judgement
  execute (CloseWith b) _          = succeedWith0 () (T.judgement $ yesNoCert b)


simple sl un gr mi =
  sliceWhen (const $ sl == Slice)
  .>>> try unsatRules
  .>>> try unsatPaths
  .>>> try unreachableRules
  .>>> fromIts
  .>>> addSinks
  .>>> when (un == Unfold) unfold
  .>>> decompose gr
  .>>> abstractSize mi
  .>>> abstractFlow
  .>>> analyse
  .>>> close

strategic gr mi =
  sliceWhen ((> 12) . length . args . startterm_)
  .>>> try unsatRules
  .>>> try unreachableRules
  .>>> ranking .<|> lare
  where
  ranking =
    try unsatPaths
    .>>> try unreachableRules
    .>>> try boundTrivialSCCs
    .>>> rank
  lare =
    (unsatPaths .>>> fromIts .>>> unfold) .<|> fromIts
    .>>> addSinks
    .>>> decompose gr
    .>>> abstractSize mi
    .>>> abstractFlow
    .>>> analyse
    .>>> close

unlimited =
  goal $
    ranking :
    (sliceWhen (const True) .>>> ranking) :
      [ simple s u g m
      | s <- [Slice, NoSlice]
      , u <- [Unfold, NoUnfold]
      , g <- [Greedy, NoGreedy]
      , m <- [Minimize, NoMinimize] ]
  where
  goal sts = best cmpTimeUB [ timeoutRemaining st | st <- sts ]
  ranking  = try unsatRules .>>> try unsatPaths .>>> try unreachableRules .>>> try boundTrivialSCCs .>>> rank

