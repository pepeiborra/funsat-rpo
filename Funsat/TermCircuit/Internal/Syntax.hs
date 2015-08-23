{-# LANGUAGE NoMonomorphismRestriction #-}
module Funsat.TermCircuit.Internal.Syntax where

import Funsat.ECircuit
import Prelude hiding (and,or,not)

-- ----------
-- Internal
-- ----------

(/\) = and
(\/) = or

(-->) = onlyif
(<-->) = iff

none = not . orL

infixl 8 /\,\/
infixl 7 -->
infix 6 <-->

fromLeft :: Either l r -> l
fromLeft (Left l) = l
fromLeft _ = error "fromLeft on a Right"
fromRight :: Either l r -> r
fromRight (Right r) = r
fromRight _ = error "fromRight on a Left"
