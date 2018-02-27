module Tct.Paicc.Problem
  ( Paicc(..)
  , Rules
  , Rule
  , ARule(..)
  , ATerm(..)
  , RuleId
  , TGraph
  , Fun
  , Var
  , Signature
  , fromIts
  ) where

import           Data.IntMap.Strict           as IM (elems)

import           Tct.Core.Common.Pretty       (Pretty, pretty)
import qualified Tct.Core.Common.Pretty       as PP
import           Tct.Core.Common.Xml          (Xml, empty, toXml)

import           Tct.Its.Data.Problem         (Its)
import qualified Tct.Its.Data.Problem         as I
import           Tct.Its.Data.TransitionGraph (TGraph)
import           Tct.Its.Data.Types           (ARule (..), ATerm (..), Fun, Rule, RuleId, Rules, Signature, Var)


data Paicc = Paicc
  { irules_    :: Rules
  , tgraph_    :: TGraph
  , signature_ :: Signature
  , domain_    :: [Var] }
  deriving (Show)

fromIts :: Its -> Paicc
fromIts its    = Paicc
  { irules_    = I.irules_ its
  , tgraph_    = I.tgraph_ its
  , signature_ = I.signature_ its
  , domain_    = I.domain  its }

instance Pretty Paicc where
  pretty prob = PP.vcat
    [ pp "Rules:"      $ pretty (IM.elems $ irules_ prob)
    , pp "Signature:"  $ pretty (signature_ prob)
    , pp "Rule Graph:" $ pretty (tgraph_ prob) ]
    where pp st p = PP.text st PP.<$$> PP.indent 2 p

instance Xml Paicc where
  toXml = const empty

