{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}

module Funsat.TermCircuit.WPO.POL(POL(..), pol, polM, agt, age, wF, vc) where

import Control.DeepSeq (NFData)
import Data.Foldable (Foldable, toList)
import Data.Term (Term, foldTerm, HasId1(..), vars)
import qualified Data.Term as Family
import Data.Typeable
import Funsat.ECircuit
import Funsat.TermCircuit.Internal.Syntax
import Funsat.TermCircuit.Symbols
import Funsat.TermCircuit.Ext
import Funsat.TermCircuit.WPO
import Funsat.TermCircuit.WPO.Symbols hiding (POL)
import qualified Funsat.TermCircuit.WPO.Symbols as Algebra
import Text.PrettyPrint.HughesPJClass
import Prelude hiding (fromInteger, sum)

newtype POL v a = POL { theSymbol :: WPOSymbolBase v a }
  deriving (Eq, Show, Ord, Pretty
           ,Functor, Foldable, NFData
           ,HasPrecedence, HasStatus, HasFiltering, WPOSymbol
           ,Typeable)

type instance Family.Var (POL v id) = v
type instance Family.Id  (POL v id) = id

pol :: WPOOptions -> Natural v -> SymbolFactory (POL v id) m repr
pol opts w0 b n x = runCircuitM $ polM opts w0 b n (const Algebra.POL) x
polM opts w0 b n interpretAlgebraBit x = do
  s <- wpoM b n opts interpretAlgebraBit x

  -- Enforcing the SIMP constraint
  let zero = fromInteger 0
  assertAll [ input st --> (nat c `gt` zero)
            | (st,c) <- zip (encodeSel s)
                            (encodeC s)
            ]
  -- Enforcing WMIN
  let wf = nat(encodeW s)
  assertAll[(wf `gt` nat  w0) \/
             orL [ nat sc_i `gt` zero | sc_i <- encodeC s]]

  return (POL s)

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
w = foldTerm (const w0) wF

wF t = nat(getW i) +# sum [ nat sc_i *# w_i | (sc_i, w_i) <- zip cc ww] where
    cc = getC i
    ww = toList t
    Just i = getId1 t

vc x = foldTerm (\y -> fromInteger $ if x == y then 1 else 0) f where
  f t = sum [ nat sc_i *# vc_i | (sc_i, vc_i) <- zip cc vvcc] where
    cc = getC i
    vvcc = toList t
    Just i = getId1 t
