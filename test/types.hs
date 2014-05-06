module Types where

import Control.Monad.State
import Data.Hashable
import Text.PrettyPrint.HughesPJClass
import Data.Map (Map)
import qualified Data.Map as Map

-- -------------------------
-- Test boolean Variable type
-- -------------------------

data NVar = VN Int | VB Int | User String deriving (Eq, Ord)
instance Hashable NVar where
    hash (VN i) = hash (0::Int,i)
    hash (VB i) = hash (1::Int,i)
    hash (User s) = hash s

instance Show NVar where
  show (VN i) = "vn" ++ show i
  show (VB i) = "vb" ++ show i
  show (User s) = s ++ "?"

instance Read NVar where
  readsPrec p ('v':'n':rest) = [(VN i, rest) | (i,rest) <- readsPrec 0 rest]
  readsPrec p ('v':'b':rest) = [(VB i, rest) | (i,rest) <- readsPrec 0 rest]
  readsPrec _ _ = []

instance Bounded NVar where minBound = VN 0; maxBound = VB maxBound
instance Enum NVar where
--  fromEnum (VN i) = i * 2
--  fromEnum (VB i) = (i * 2) + 1
--  toEnum i = (if odd i then VB else VN) (i `div` 2)
  toEnum i = VB i
  fromEnum (VB i) = i

-- -----------------
-- Test Ids
-- -----------------

data RandId = F | F2 | G | G2 | S | Z deriving (Eq, Enum, Ord, Show)
instance Pretty RandId where pPrint = text . show
instance Hashable RandId where hash = fromEnum


class IsDefined id where isDefined :: id -> Bool
class HasArity id where getIdArity :: id -> Int

instance IsDefined RandId where
  isDefined F = True
  isDefined G = True
  isDefined F2 = True
  isDefined G2 = True
  isDefined _  = False

instance HasArity RandId where
  getIdArity F = 1
  getIdArity G = 1
  getIdArity F2 = 2
  getIdArity G2 = 2
  getIdArity S = 1
  getIdArity Z = 0
