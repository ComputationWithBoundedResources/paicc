module Tct.Paicc.Strategies where

-- import           Tct.Core
import           Tct.Core.Common.Pretty  (Pretty, pretty)
import qualified Tct.Core.Common.Pretty  as PP
import           Tct.Core.Common.Xml     (Xml, toXml, empty)
import qualified Tct.Core.Data           as T

import           Tct.Paicc.LoopStructure
import           Tct.Paicc.Problem

-- * LoopStructure

-- | This processor tries to infer a \Loop Structure\.
-- Return @Yes@ if successful, otherwise @No@.
data LoopStructureProcessor = LoopStructure Greedy
  deriving Show

data LoopStructureProof = LoopStructureProof (Top [RuleId])
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
  toXml = const empty

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
