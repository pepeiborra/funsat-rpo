{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE RecordWildCards, NamedFieldPuns, DisambiguateRecordFields #-}
{-# LANGUAGE PatternGuards, ViewPatterns #-}
{-# LANGUAGE DeriveDataTypeable, DeriveGeneric #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE CPP #-}

module Funsat.TermCircuit.WPO.Symbols where

import Control.DeepSeq
import Control.Exception as CE
import Control.Monad (forM, forM_, replicateM)
import Control.Monad.Trans (MonadTrans, lift)
import Data.Foldable(Foldable(foldMap))
import Data.List (transpose)
import qualified Data.Term       as Family
import Data.Typeable
import Funsat.ECircuit
import Funsat.TermCircuit
import Funsat.TermCircuit.WPO
import Funsat.TermCircuit.Ext
import Funsat.TermCircuit.Internal.Syntax
import Funsat.TermCircuit.Symbols
import GHC.Generics
import Text.PrettyPrint.HughesPJClass
import Prelude hiding (and,not,or,fromInteger)
import qualified Prelude as P

-- ----------------------------------------------
-- Symbol type carrying the result of a solution
-- ----------------------------------------------

data Algebra = SUM | POL | MAX deriving (Eq, Ord, Show, Typeable)

data SymbolRes a = SymbolRes { theSymbolR   :: a
                             , prec         :: Int
                             , weight       :: Int
                             , status       :: Status
                             , cs           :: [Int]
                             , cp           :: [Int]
                             , algebra      :: Algebra
                             }
  deriving (Eq, Ord, Show, Typeable, Generic)

instance Functor SymbolRes where fmap f SymbolRes{..} = SymbolRes{theSymbolR = f theSymbolR, ..}

instance Pretty a => Pretty (SymbolRes a) where pPrint = pPrint . theSymbolR

data Status   = Lex ([Maybe Int]) deriving (Eq, Ord, Show)

mkStatus :: [Bool] -> [[Bool]] -> Status
mkStatus sel perm =
 CE.assert (all oneOrNone perm) $
 CE.assert (all oneOrNone (transpose perm)) $
    Lex ([ if P.not sel_i then Nothing else
            Just ( head ([ i
                         | (i,True) <- zip [1..] perm_i
                         ] ++ [-1]))
         | (sel_i, perm_i) <- zip sel perm])

  where
    oneOrNone []         = True
    oneOrNone (False:xx) = oneOrNone xx
    oneOrNone (True:xx)  = P.not $ P.or xx

--mkSymbolDecoder :: (Ord v, Show v, Show id)=> id -> v -> Natural v -> [Natural v] -> [Natural v] -> [v] -> [[v]] -> EvalM v (SymbolRes id)
mkSymbolDecoder the_id interpretAlgebraBit algebra n_n w_n cs_nn cp_nn sel_bb perm_bb = do
                 n          <- evalNat n_n
                 w          <- evalNat w_n
                 cs         <- mapM evalNat cs_nn
                 cp         <- mapM evalNat cp_nn
                 sel        <- mapM evalVar sel_bb
                 perm       <- mapM (mapM evalVar) perm_bb
                 alg        <- evalVar algebra
                 let statusMsg   = mkStatus sel perm
                 return (SymbolRes the_id n w statusMsg cs cp
                           (interpretAlgebraBit alg))
  where
   evalVar = evalB . input
   evalNat = evalN . nat

-- ------------------------
-- Basetype for WPO Symbols
-- ------------------------

data WPOSymbolBase v a =
     Symbol  { theSymbol     :: a
             , encodePrec    :: Natural v
             , encodePerm    :: [[v]]
             , encodeSel     :: [v]
             , encodeW       :: Natural v
             , encodeC       :: [Natural v]
             , encodeP       :: [Natural v]
             , encodeAlgebra :: v -- 0 for POL and 1 for MAX
             , decodeSymbol  :: EvalM v (SymbolRes a)
             }
   deriving (Show, Typeable, Generic)

instance Pretty a => Pretty (WPOSymbolBase v a) where pPrint = pPrint . theSymbol

instance Eq   a => Eq   (WPOSymbolBase v a) where
    a@Symbol{} == b@Symbol{} = theSymbol a == theSymbol b

instance Ord a => Ord (WPOSymbolBase v a) where
   compare a b = theSymbol a `compare` theSymbol b

instance Functor (WPOSymbolBase v) where
    fmap f Symbol{..} = Symbol{theSymbol = f theSymbol,
                               decodeSymbol = (fmap.fmap) f decodeSymbol, ..}
instance Foldable (WPOSymbolBase v) where foldMap f Symbol{..} = f theSymbol

instance HasPrecedence (WPOSymbolBase v a) where precedence_v = encodePrec
instance HasStatus     (WPOSymbolBase v a) where lexPerm_vv   = Just . encodePerm
instance HasFiltering  (WPOSymbolBase v a) where filtering_vv = encodeSel
instance WPOSymbol     (WPOSymbolBase v a) where
  getW = encodeW
  getC = encodeC
  getP = encodeP
  getAlg = encodeAlgebra

instance (NFData v, NFData a) => NFData(WPOSymbolBase v a)

data WPORange  = Fixed Integer
               | Variable (Maybe Integer) (Maybe Integer)
               deriving(Typeable, Generic, Show)

data WPOStatus = Empty | Total | Partial deriving (Typeable, Generic, Show)

data WPOOptions =
  WPOOptions { constants, coefficients :: WPORange
             , statusType :: WPOStatus
--             , allowQuasiPrecedence :: Bool
             } deriving (Typeable, Generic, Show)

wpoOptions = WPOOptions
             { constants    = Variable Nothing Nothing
             , coefficients = Variable Nothing Nothing
             , statusType   = Partial }

wpoM :: ( MonadCircuit (t m), MonadTrans t
         , Show (Var (t m)), Show a, Ord (Var (t m)), Monad m) =>
         (String -> m(Var (t m))) ->
         (String -> m(Natural (Var (t m)))) ->
         WPOOptions ->
         (Bool -> Algebra) ->
         (a, Int) ->
         t m (WPOSymbolBase (Var (t m)) a)
wpoM booleanm naturalm WPOOptions{..} interpretAlgebraBit (x, ar) = do
  n_b      <- natural ("prec_" ++ show x)
  w        <- natural ("w_" ++ show x)
  perm_bb  <- replicateM ar (replicateM ar (boolean ("perm_" ++ show x)))
  sel_bb   <- replicateM ar (boolean ("sel_" ++ show x))
  c_bb     <- forM [1..ar] $ \i -> (natural $ show x ++ "_c_" ++ show i)
  p_bb     <- forM [1..ar] $ \i -> (natural $ show x ++ "_p_" ++ show i)
  algebra  <- boolean ("max_" ++ show x)
  let perm_ee = (fmap.fmap) input perm_bb
  let sel_ee  = map input sel_bb

  -- Precedence invariant
  -- --------------------
  assertAll [ nat n_b `ge` fromInteger 0 ]

  -- Permutation invariants
  -- -----------------------

  -- ST: There is one or zero arguments considered at the k'th perm position,
  assertAll [ (sel_k /\ one perm_k) \/ (not sel_k /\ zero perm_k)
              | (sel_k, perm_k) <- zip sel_ee (transpose perm_ee)]

  -- There is one more condition to ensure that  algebra is weakly simple w.r.t. the status
  -- This condition (called SIMP in the WPO thesis) is not definable here, as it is algebra dependent

  -- WPO encoding options
  -- --------------------
  case statusType of
     Total -> assertAll sel_ee
     Empty -> assertAll [none sel_ee]
     Partial -> return ()

  case constants of
     Fixed i -> do
       let cond p = nat p `eq` fromInteger i
       assertAll (map cond p_bb)
     Variable minV maxV ->
       forM_ p_bb $ \p -> do
         let np = nat p
         case minV of Just i -> assertAll [np `gt` fromInteger i] ; _ -> return ()
         case maxV of Just i -> assertAll [fromInteger i `gt` np] ; _ -> return ()

  case coefficients of
     Fixed i -> do
       let cond p = nat p `eq` fromInteger i
       assertAll (map cond c_bb)
     Variable minV maxV ->
       forM_ c_bb $ \p -> do
         let np = nat p
         case minV of Just i -> assertAll [np `gt` fromInteger i] ; _ -> return ()
         case maxV of Just i -> assertAll [fromInteger i `gt` np] ; _ -> return ()

  return $
             Symbol
             { theSymbol    = x
             , encodePrec   = n_b
             , encodePerm   = perm_bb
             , encodeSel    = sel_bb
             , encodeC      = c_bb
             , encodeP      = p_bb
             , encodeW      = w
             , encodeAlgebra= algebra
             , decodeSymbol = mkSymbolDecoder x interpretAlgebraBit algebra n_b w c_bb p_bb sel_bb perm_bb}
  where
    boolean = lift . booleanm
    natural = lift . naturalm
    zero    = not . orL

-- ----------------------
-- Term family membership
-- ----------------------
type instance Family.Var (WPOSymbolBase  v id) = v
type instance Family.Id  (WPOSymbolBase  v id) = id
