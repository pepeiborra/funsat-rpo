{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RecordWildCards, NamedFieldPuns #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}

module Funsat.TermCircuit.WPO.SUM(SUM(..), SUMOptions(..), WPOStatus(..), sum, agt, age) where

import Control.DeepSeq (NFData)
import Data.Foldable (Foldable)
import Data.Term (Term, foldTerm, HasId1(..), vars)
import qualified Data.Term as Family
import Data.Typeable
import Funsat.ECircuit hiding (sum)
import qualified Funsat.ECircuit as Fun
import Funsat.TermCircuit.Internal.Syntax
import Funsat.TermCircuit.Symbols
import Funsat.TermCircuit.Ext
import Funsat.TermCircuit.WPO
import Funsat.TermCircuit.WPO.Symbols (WPOOptions(..), WPOStatus(..), WPORange(..))
import qualified Funsat.TermCircuit.WPO.Symbols as Algebra
import Funsat.TermCircuit.WPO.POL (POL(..), polM)
import Text.PrettyPrint.HughesPJClass
import Prelude hiding (fromInteger, sum)
import Data.Foldable (toList)

newtype SUM v a = SUM { theSymbol :: POL v a }
  deriving (Eq, Show, Ord, Pretty
           ,Functor, Foldable, NFData
           ,HasPrecedence, HasStatus, HasFiltering, WPOSymbol
           ,Typeable)

type instance Family.Var (SUM v id) = v
type instance Family.Id  (SUM v id) = id

data SUMOptions = SUMOptions { statusType :: WPOStatus }

sum :: SUMOptions -> Natural v -> SymbolFactory (SUM v id) m repr
sum SUMOptions{..} w0 b n x = runCircuitM $ sumM opts' w0 b n x where
  opts' = WPOOptions{statusType, coefficients = Fixed 0, constants = Fixed 0}

sumM opts w0 b n x = do
  POL s <- polM opts w0 b n (const Algebra.SUM) x

  -- Fix the coefficients to 1
  let one = fromInteger 1
  assertAll [ eq (nat c) one | c <- getC s ]

  -- Fix w0
  assertAll [nat w0 `eq` fromInteger 0]

  return (SUM $ POL s)


agt,age ::( termF ~ Family.TermF repr
          , id    ~ Family.Id termF
          , v     ~ Family.Var id
          , WPOCircuit repr, Co repr v
          , HasId1 termF, Functor termF, Foldable termF
          , WPOSymbol id, WPOAlgebra repr
          , Eq v'
          ) => Term termF v' -> Term termF v' -> repr v
agt s t = (w s `gt` w t) /\ andL [ vc x s `ge` vc x t | x <- vars t]
age s t = (w s `ge` w t) /\ andL [ vc x s `ge` vc x t | x <- vars t]

w :: ( WPOSymbol (Family.Id t)
     , WPOCircuit repr
     , HasId1 t, Foldable t, Co repr v
     , Functor t
     , id ~ Family.Id t
     , v ~ Family.Var id
     ) => Term t a -> repr v
w = foldTerm (const w0) f where
  f t = nat(getW i) +# Fun.sum (toList t) where
    Just i = getId1 t

vc x = foldTerm (\y -> fromInteger $ if x == y then 1 else 0) (Fun.sum . toList)
