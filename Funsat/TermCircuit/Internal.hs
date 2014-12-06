{-# LANGUAGE FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}

module Funsat.TermCircuit.Internal where

import Funsat.ECircuit as Funsat
import Prelude hiding (and,or)

(/\) = and
(\/) = or

(-->) = onlyif
(<-->) = iff

none = Funsat.not . orL

infixl 8 /\,\/
infixl 7 -->
infix 6 <-->

fromLeft :: Either l r -> l
fromLeft (Left l) = l
fromLeft _ = error "fromLeft on a Right"
fromRight :: Either l r -> r
fromRight (Right r) = r
fromRight _ = error "fromRight on a Left"
