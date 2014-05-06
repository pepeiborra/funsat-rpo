{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE RecordWildCards, NamedFieldPuns, DisambiguateRecordFields #-}
{-# LANGUAGE PatternGuards, ViewPatterns #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE CPP #-}

module Funsat.RPOCircuit.Symbols (
  rpos, RPOSsymbol(..),
  rpo,  RPOsymbol(..),
  lpos, LPOSsymbol(..),
  lpo,  LPOsymbol(..),
  mpo,  MPOsymbol(..),
  Natural(..),
  SymbolRes(..), mkSymbolDecoder,
  Status(..), mkStatus
  ) where

import           Control.Arrow
import qualified Control.Exception                 as CE
import           Control.Monad
import           Control.Monad.Writer
import           Data.Foldable                     (Foldable, foldMap)
import           Data.List                         (transpose)
import qualified Data.Term                         as Family
import           Data.Typeable

import           Funsat.RPOCircuit
import           Funsat.ECircuit                   hiding (not,or)
import qualified Funsat.ECircuit                   as C
import           Funsat.RPOCircuit.Internal

#ifdef DEBUG
import           Control.Monad.Identity
#endif
import Control.Applicative (Applicative)
import Text.PrettyPrint.HughesPJClass (Pretty(..))

-- ----------------------------
-- Type for natural variables
-- ----------------------------

newtype Natural v = Natural {encodeNatural::v} deriving (Eq,Ord,Show)

-- ----------------------------------------------
-- Symbol type carrying the result of a solution
-- ----------------------------------------------

data SymbolRes a = SymbolRes { theSymbolR :: a
                             , prec       :: Int
                             , status     :: Status
                             , filtering  :: Either Int [Int] }
  deriving (Eq, Ord, Show, Typeable)

instance Functor SymbolRes where fmap f SymbolRes{..} = SymbolRes{theSymbolR = f theSymbolR, ..}

instance Pretty a => Pretty (SymbolRes a) where pPrint = pPrint . theSymbolR

mkSymbolDecoder :: (Ord v, Show v, Show id
                   )=> id -> Natural v -> v -> [v] -> [[v]] -> v -> EvalM v (SymbolRes id)
mkSymbolDecoder the_id n_b list_b pos_bb perm_bb mset = do
                 n          <- evalNat n_b
                 isList     <- evalVar list_b
                 pos        <- mapM evalVar pos_bb
                 status     <- evalVar mset
                 perm_bools <- mapM (mapM evalVar) perm_bb
                 let the_positions = [fromInteger i | (i,True) <- zip [1..] pos]
                     statusMsg   = mkStatus status perm_bools
                 return$
                  if not isList
                   then CE.assert (length the_positions == 1)
                        (SymbolRes the_id n statusMsg (Left $ headS the_positions))
                   else (SymbolRes the_id n statusMsg (Right the_positions))
  where
   headS [] = error ("mkSymbolDecoder: invalid null collapsing AF for  (" ++ show the_id ++ ")")
   headS (x:_) = x

   evalVar = evalB . input
   evalNat = evalN . nat . encodeNatural

-- -------
-- Status
-- -------

data Status   = Mul | Lex (Maybe [Int]) deriving (Eq, Ord, Show)

mkStatus :: Bool -> [[Bool]] -> Status
mkStatus mul perm
 | mul       = Mul
 | otherwise = CE.assert (all oneOrNone perm) $
               CE.assert (all oneOrNone (transpose perm)) $
               Lex (Just [ head ([i | (i,True) <- zip [1..] perm_i] ++ [-1])
                          | perm_i <- perm])

  where
    oneOrNone []         = True
    oneOrNone (False:xx) = oneOrNone xx
    oneOrNone (True:xx)  = not $ or xx

-- --------------------------------
-- Typing untyped circuits
-- --------------------------------

newtype SomeCircuit v = SomeCircuit { unC :: forall repr . (Circuit repr, OneCircuit repr, ECircuit repr, Co repr v) => repr v }

liftSomeCircuit :: (forall repr . (ECircuit repr, Co repr v) => repr v -> repr v) -> SomeCircuit v -> SomeCircuit v
liftSomeCircuit  f (SomeCircuit x) = SomeCircuit (f x)
liftSomeCircuit2 :: (forall repr . (ECircuit repr, Co repr v) => repr v -> repr v -> repr v) -> SomeCircuit v -> SomeCircuit v -> SomeCircuit v
liftSomeCircuit2 f (SomeCircuit x) (SomeCircuit y) = SomeCircuit (f x y)

instance Circuit SomeCircuit where
  type Co SomeCircuit v = ()
  true = SomeCircuit true
  false = SomeCircuit false
  input v = SomeCircuit (input v)
  not = liftSomeCircuit C.not
  and = liftSomeCircuit2 C.and
  or  = liftSomeCircuit2 C.or

instance OneCircuit SomeCircuit where
  one xx = SomeCircuit (one $ map unC xx)

instance ECircuit SomeCircuit where
  onlyif = liftSomeCircuit2 C.onlyif
  iff = liftSomeCircuit2 C.iff
  xor = liftSomeCircuit2 C.xor
  ite (SomeCircuit a) (SomeCircuit b) (SomeCircuit c) = SomeCircuit (ite a b c)

-- -------------------------------------------------
-- Generic encoding of RPO symbols with AF
-- -------------------------------------------------

type SymbolFactory s = (Monad m, ECircuit repr, OneCircuit repr, Co repr v
                       ,Show id, Ord v, Show v
                       ) =>
                        m v -> m(Natural v) -> (id, Int) -> m(s v id, repr v)

class Monad m => MonadCircuit m where
  type Var m
  assertAll :: [SomeCircuit (Var m)] -> m ()

newtype CircuitM v m a = CircuitM {unCircuitM::WriterT [SomeCircuit v] m a}
    deriving (Applicative, Functor, Monad, MonadTrans)

runCircuitM :: (Co repr v, OneCircuit repr, ECircuit repr, Monad m) => CircuitM v m a -> m (a, repr v)
runCircuitM = liftM (second (unC . andL)) . runWriterT . unCircuitM

instance Monad m => MonadCircuit (CircuitM v m) where
  type Var (CircuitM v m) = v
  assertAll x = CircuitM $ tell x


data RPOSsymbol v a = Symbol { theSymbol    :: a
                             , encodePrec   :: v
                             , encodeAFlist :: v
                             , encodeAFpos  :: [v]
                             , encodePerm   :: [[v]]
                             , encodeUseMset:: v
                             , decodeSymbol :: EvalM v (SymbolRes a)}
   deriving Show

instance Show (EvalM v a) where show _ = "evalM computation"

instance Pretty a => Pretty (RPOSsymbol v a) where pPrint = pPrint . theSymbol

instance Eq   a => Eq   (RPOSsymbol v a) where
    a@Symbol{} == b@Symbol{} = theSymbol a == theSymbol b

instance Ord a => Ord (RPOSsymbol v a) where
   compare a b = theSymbol a `compare` theSymbol b

instance Functor (RPOSsymbol v) where
    fmap f Symbol{..} = Symbol{theSymbol = f theSymbol,
                               decodeSymbol = (fmap.fmap) f decodeSymbol, ..}
instance Foldable (RPOSsymbol v) where foldMap f Symbol{..} = f theSymbol

instance HasPrecedence (RPOSsymbol v a) where precedence_v = encodePrec
instance HasStatus     (RPOSsymbol v a) where
    useMul_v   = encodeUseMset
    lexPerm_vv = Just . encodePerm

instance HasFiltering (RPOSsymbol v a) where
    listAF_v   = encodeAFlist
    filtering_vv = encodeAFpos

rpos :: SymbolFactory RPOSsymbol
rpos b n = runCircuitM . rposM b n

rposM :: (MonadCircuit (t m), MonadTrans t, Show (Var (t m)), Show a, Ord (Var (t m)), Monad m) =>
         m (Var (t m)) -> m (Natural (Var (t m))) -> (a, Int) -> t m (RPOSsymbol (Var (t m)) a)
rposM booleanm naturalm (x, ar) = do
  n_b      <- natural
  perm_bb  <- replicateM ar (replicateM ar boolean)
  mset     <- boolean
  (list_b:pos_bb) <- case ar of
                       0 -> do {lb <- boolean; assertAll [input lb]; return [lb]}
                       _ -> replicateM (ar + 1) boolean

  let (list_e:pos_ee) = fmap input (list_b:pos_bb)
      perm_ee = (fmap.fmap) input perm_bb

--  when (P.not defined || isDPSymbol x) $ assert [not $ usable_e]

  -- Filtering invariants
  assertAll [ C.not list_e --> one pos_ee ]

  -- Permutation invariants
  -- -----------------------

  -- There is one or zero arguments considered at the k'th perm position,
  assertAll [ orL perm_k --> one perm_k
              | perm_k <- transpose perm_ee]
--  assertAllM [ not p ==> and (not <$> perm_i) | (p, perm_i) <- zip pos_ee perm_ee]

  -- Non filtered arguments are considered at exactly one position in the permutation
  -- Filtered arguments may not be used in the permutation
  assertAll [ ite p (one perm_i) (C.not $ orL perm_i)
                  | (p, perm_i) <- zip pos_ee perm_ee]

  -- All non-filtered arguments are permuted 'to the left'
  assertAll [ orL perm_k1 --> orL perm_k
                  | (perm_k, perm_k1) <- zip (transpose perm_ee) (tail $transpose perm_ee)]

  return $
             Symbol
             { theSymbol    = x
             , encodePrec   = encodeNatural n_b
             , encodeAFlist = list_b
             , encodeAFpos  = pos_bb
             , encodePerm   = perm_bb
             , encodeUseMset= mset
             , decodeSymbol = mkSymbolDecoder x n_b list_b pos_bb perm_bb mset}
  where
    (-->)   = onlyif
    boolean = lift booleanm
    natural = lift naturalm

-- ----------------------
-- Term family membership
-- ----------------------
type instance Family.Var (RPOSsymbol  v id) = v
type instance Family.Var (RPOsymbol   v id) = v
type instance Family.Var (LPOSsymbol  v id) = v
type instance Family.Var (LPOsymbol   v id) = v
type instance Family.Var (MPOsymbol   v id) = v

type instance Family.Id (RPOSsymbol  v id) = id
type instance Family.Id (RPOsymbol   v id) = id
type instance Family.Id (LPOSsymbol  v id) = id
type instance Family.Id (LPOsymbol   v id) = id
type instance Family.Id (MPOsymbol   v id) = id

-- --------
-- Variants
-- --------

-- LPO with status

newtype LPOSsymbol v a = LPOS{unLPOS::RPOSsymbol v a}
    deriving (Eq, Ord, Show, Pretty
             ,HasPrecedence, HasStatus, HasFiltering
             ,Functor, Foldable)

lpos :: SymbolFactory LPOSsymbol
lpos b n = runCircuitM . lposM b n
lposM boolean natural x = do
  s <- rposM boolean natural x
  assertAll [C.not $ useMul s]
  return $ LPOS s

-- LPO

newtype LPOsymbol v a = LPO{unLPO::RPOSsymbol v a}
    deriving (Eq, Ord, Show, Pretty
             ,HasPrecedence, HasFiltering
             ,Functor, Foldable)


lpo :: SymbolFactory LPOsymbol
lpo b n x = runCircuitM $ do
  s <- rposM b n x
  assertAll [C.not $ useMul s]
  return (LPO s)

instance () => HasStatus (LPOsymbol v a) where
    useMul_v     = encodeUseMset . unLPO
    lexPerm_vv _ = Nothing

-- MPO
newtype MPOsymbol v a = MPO{unMPO::RPOSsymbol v a}
    deriving (Eq, Ord, Show, Pretty
             ,HasPrecedence, HasStatus, HasFiltering
             ,Functor, Foldable)

mpo :: SymbolFactory MPOsymbol
mpo b n x = runCircuitM $ do
  s <- rposM b n x
  assertAll [useMul  s]
  return (MPO s)

-- RPO
newtype RPOsymbol v a = RPO{unRPO::RPOSsymbol v a}
    deriving (Eq, Ord, Show, Pretty
             ,HasPrecedence, HasStatus, HasFiltering
             ,Functor, Foldable)

rpo :: SymbolFactory RPOsymbol
rpo b n x = runCircuitM $ do
  s <- rposM b n x
  return (RPO s)



-- Testing

#ifdef DEBUG

test = runIdentity $ rpos (return (1::Int)) (return $ Natural 2) ("f", 2)

#endif
