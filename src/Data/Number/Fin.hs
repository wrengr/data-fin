{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2013.07.20
-- |
-- Module      :  Data.Number.Fin
-- Copyright   :  2012--2013 wren gayle romano
-- License     :  BSD3
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Newtypes of built-in numeric types for finite subsets of the
-- natural numbers. The default implementation is the newtype of
-- 'Integer', since the type-level numbers are unbounded so this
-- is the most natural. Alternative implementations are available
-- as nearly drop-in replacements. The reason for using modules
-- that provide the same API, rather than using type classes or
-- type families, is that those latter approaches introduce a lot
-- of additional complexity for very little benefit. Using multiple
-- different representations of finite sets in the same module seems
-- like an uncommon use case. Albeit, this impedes writing
-- representation-agnostic functions...
--
-- When the underlying type can only represent finitely many values,
-- this introduces many corner cases which makes reasoning about
-- programs more difficult. However, the main use case for these
-- finite representations is because we know we'll only be dealing
-- with \"small\" sets, so we'll never actually encounter the corner
-- cases. Thus, this library does not try to handle the corner
-- cases, but rather rules them out with the type system.
--
-- Many of the operations on finite sets arise from the (skeleton
-- of the) augmented simplex category. For example, the ordinal-sum
-- functor provides the monoidal structure of that category. For
-- more details on the mathematics, see
-- <http://ncatlab.org/nlab/show/simplex+category>.
----------------------------------------------------------------
module Data.Number.Fin (module Data.Number.Fin.Integer) where
import Data.Number.Fin.Integer

----------------------------------------------------------------
----------------------------------------------------------------

-- TODO: offer a newtype of 'Fin' (e.g., @IntMod@) which offers a 'Num' instance for modular arithmetic.

{-
-- TODO: make Fin a newtype family indexed by the representation type it's a newtype of (e.g., "Data.Number.Fin.Integer" would be @Fin Integer n@)? That would allow people to be polymorphic over the different representations. This would also work great with @Int `Mod` n@ for the modular arithmetic!

However, note that this means we can't use the @reflection@ package because the 'Reifies' class has a fundep. Unless we always want to reflect as 'Integer' and then do 'fromInteger' everywhere... surely the fundep is there for a reason, but why? We could get around this with the 'OfType' branch of reflection we've been working on...
-}

----------------------------------------------------------------
----------------------------------------------------------- fin.
