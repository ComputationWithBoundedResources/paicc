module Tct.Paicc 
  ( Paicc(..)
  , fromIts
  , unfold
  , addSinks
  , Decomposition
  , decompose
  , SizeAbstraction
  , abstractSize
  , FlowAbstraction
  , abstractFlow
  , analyse
  , Minimize(..)
  , Greedy(..)
  ) where

import Control.Monad (when)
import           Tct.Core.Common.Pretty  (Pretty, pretty)
import qualified Tct.Core.Common.Pretty  as PP
import qualified Tct.Core.Common.Xml     as Xml
import           Tct.Core.Common.Xml     (Xml, toXml)
import qualified Tct.Core.Data           as T


import          Tct.Its (Its)
import          Tct.Its.Data.LocalSizebounds (Minimize(..))

import qualified Lare.Analysis                    as LA
import qualified Lare.Flow                        as LA
import qualified Lare.Tick                        as LA

import          Tct.Paicc.Problem hiding (fromIts)
import qualified Tct.Paicc.Problem as P (fromIts)
import          Tct.Paicc.Decomposition (inferWith, isComplete, Greedy(..), Top, draw)
import          Tct.Paicc.Abstraction
import qualified Tct.Paicc.Preprocessor as P


-- * Strategies

type a ~> b = T.Strategy a b

fromIts :: Its ~> Paicc
fromIts = T.processor FromIts

unfold, addSinks :: Paicc ~> Paicc
unfold   = T.processor Unfold
addSinks = T.processor AddSinks

decompose :: Greedy -> Paicc ~> Decomposition
decompose greedy = T.processor (Decompose greedy)

abstractSize :: Minimize -> Decomposition ~> SizeAbstraction
abstractSize minimize = T.processor (AbstractSize UseCFG minimize)

abstractFlow :: SizeAbstraction ~> FlowAbstraction
abstractFlow = T.processor AbstractFlow

analyse :: FlowAbstraction ~> ()
analyse = T.processor LareProcessor


-- * Preprocessing

data FromIts = FromIts deriving Show

instance T.Processor FromIts where
  type ProofObject FromIts = ()
  type In          FromIts = Its
  type Out         FromIts = Paicc
  type Forking     FromIts = T.Id

  execute FromIts prob = T.succeedWithId () (P.fromIts prob)

data AddSinks = AddSinks deriving Show

instance T.Processor AddSinks where
  type ProofObject AddSinks = ()
  type In          AddSinks = Paicc
  type Out         AddSinks = Paicc
  type Forking     AddSinks = T.Id

  execute AddSinks prob = T.succeedWithId () (P.addSinks prob)

data Unfold = Unfold deriving Show

instance T.Processor Unfold where
  type ProofObject Unfold = ()
  type In          Unfold = Paicc
  type Out         Unfold = Paicc
  type Forking     Unfold = T.Id

  execute Unfold prob = T.succeedWithId () (P.unfold prob)


-- * Decompose

newtype Decompose = Decompose Greedy deriving Show

newtype DecomposeProof = DecomposeProof (Top [RuleId])
  deriving Show

type Decomposition = (Paicc, DecomposeProof)

instance Pretty DecomposeProof where
  pretty (DecomposeProof t)= PP.vcat
    [ PP.text "We construct a looptree:"
    , PP.indent 2 $ PP.vcat $ PP.text <$> draw t ]

instance Xml DecomposeProof where
  toXml = Xml.text . show . pretty

instance T.Processor Decompose where
  type ProofObject Decompose = DecomposeProof
  type In          Decompose = Paicc
  type Out         Decompose = Decomposition
  type Forking     Decompose = T.Id

  execute (Decompose greedy) prob = do
    tree <- inferWith greedy prob
    let proof = DecomposeProof tree
    if isComplete tree
      then T.succeedWithId proof (prob,proof)
      else T.abortWith proof


-- * Abstract

data AbstractSize = AbstractSize UseGraph Minimize 
  deriving Show

instance Xml (Paicc, DecomposeProof) where toXml = Xml.text . show . pretty

instance T.Processor AbstractSize where
  type ProofObject AbstractSize = ()
  type In          AbstractSize = Decomposition
  type Out         AbstractSize = SizeAbstraction
  type Forking     AbstractSize = T.Id

  execute (AbstractSize usegraph minimize) (prob, DecomposeProof tree) =
    T.succeedWithId () =<< toLareM prob usegraph minimize tree

data AbstractFlow = AbstractFlow deriving Show

instance Xml SizeAbstraction where toXml = Xml.text . show . pretty
instance Xml FlowAbstraction where toXml = Xml.text . show . pretty
instance Xml LareProof where toXml = Xml.text . show . pretty
instance Pretty LareProof where pretty (LareProof p) = pretty p


instance T.Processor AbstractFlow where
  type ProofObject AbstractFlow = ()
  type In          AbstractFlow = SizeAbstraction
  type Out         AbstractFlow = FlowAbstraction
  type Forking     AbstractFlow = T.Id

  execute AbstractFlow (Program vs prob) = T.succeedWithId () $ Program vs' (LA.toFlow vs' prob)
    where vs' = LA.Counter: LA.Huge : LA.K : vs


-- * LareAnalyise

data LareProcessor = LareProcessor deriving Show
newtype LareProof = LareProof Proof deriving Show

instance T.Processor LareProcessor where
  type ProofObject LareProcessor = LareProof
  type In LareProcessor          = FlowAbstraction
  type Out LareProcessor         = ()
  type Forking LareProcessor     = T.Judgement

  execute LareProcessor (Program vs prob) =
    let
      proofM = do
        -- proof <- LA.convertWith (LA.ticked $ LA.flow vs) prob
        proof <- Right $ LA.convert (LA.ticked $ LA.flow vs) prob
        let bound = LA.boundOfProof proof
        when (bound == LA.Indefinite) (Left "Unknown bound.")
        return (proof, bound)
    in
    either
      T.abortWith
      (\(proof, bound) -> T.succeedWith0 (LareProof proof) (T.judgement $ T.timeUBCert $ toComplexity bound))
      proofM


toComplexity :: LA.Complexity -> T.Complexity
toComplexity LA.Indefinite = T.Unknown
toComplexity LA.Constant   = T.Poly (Just 0)
toComplexity LA.Linear     = T.Poly (Just 1)
toComplexity LA.Polynomial = T.Poly Nothing
toComplexity LA.Primrec    = T.Primrec

-- * Misc


newtype LoopStructureProcessor = LoopStructure Greedy
  deriving Show

newtype LoopStructureProof = LoopStructureProof (Top [RuleId])
  deriving Show

instance T.Processor LoopStructureProcessor where
  type ProofObject LoopStructureProcessor = LoopStructureProof
  type In LoopStructureProcessor          = Paicc
  type Out LoopStructureProcessor         = Paicc
  type Forking LoopStructureProcessor     = T.Judgement

  execute (LoopStructure greedy) prob = do
    tree <- inferWith greedy prob
    T.succeedWith0 (LoopStructureProof tree) (const $ T.yesNoCert $ isComplete tree)

instance Pretty LoopStructureProof where
  pretty (LoopStructureProof t)= PP.vcat
    [ PP.text "We construct a looptree:"
    , PP.indent 2 $ PP.vcat $ PP.text <$> draw t ]

instance Xml LoopStructureProof where
  toXml = const Xml.empty

-- instance PP.Pretty CycleManiaProof where
--   pretty (CycleManiaProof proofs) = PP.vcat
--     [ PP.text "We rank cyclic paths:"
--     , PP.text "Solved Problems:"
--     , PP.indent 2 $ PP.itemise (PP.char '-') $ flip map solved $ \(its,order) ->
--       PP.vcat
--        [ PP.text "Problem:"
--        , PP.indent 2 $ PP.pretty its
--        , PP.text "Rank:"
--        , PP.indent 2 $ PP.pretty order ]
--     , PP.text "Open Problems:"
--     , PP.indent 2 $ PP.itemise' (PP.char '-') open
--     ]
--     where
--     (open, solved) = partitionEithers proofs

-- instance Xml.Xml CycleManiaProof where
--   toXml = Xml.text . show
