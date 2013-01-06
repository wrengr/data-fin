{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
{-# LANGUAGE EmptyDataDecls
           , RankNTypes
           , ScopedTypeVariables
           , MultiParamTypeClasses
           #-}
----------------------------------------------------------------
--                                                    2013.01.05
-- |
-- Module      :  Data.Reflection.OfType
-- Copyright   :  2012--2013 wren ng thornton,
--                2009-2012 Edward Kmett,
--                2012 Elliott Hird,
--                2004 Oleg Kiselyov and Chung-chieh Shan
-- License     :  BSD3
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  experimental
-- Portability :  semi-portable (RankNTypes, MPTCs)
--
-- A fork of @reflection-1.1.6@ for removing the fundep.
----------------------------------------------------------------
module Data.Reflection.OfType
    (
    -- * Reification of type signature annotations
      OfType()
    , the
    -- * Existential hiding of reified values
    , Exists()
    , runExists
    , exists
    , choose
    -- * Reflection
    , IsOfType(reflect_)
    , reflect
    , reify
    , reifys
    ) where

import Data.Proxy (Proxy(Proxy))

----------------------------------------------------------------
-- | Values of type @x\`OfType\`a@ are proofs that (the reflection
-- of) @x@ has type @a@. Of course there's an easy proof: the
-- reflection of @x@ as an actual value of type @a@; hence, this
-- is a singleton type whose only value is the reflection of @x@
-- at type @a@. The name is chosen to support infix use. And, indeed,
-- you can use it infix (provided @TypeOperators@ is enabled).
--
-- The 'Read' instance is only provided because we can. However,
-- note that it is exceptionally weak since you can only read things
-- you could've gotten from 'reflect' anyways, and it's more expensive
-- since we need to check that the read value is equal to @x@.
newtype OfType x a = OfType a
    deriving (Show, Eq, Ord)
    -- N.B., do not export the constructor; else this is equivalent
    -- to @Tagged x a@, which allows people to change the tag!
    --
    -- N.B., because it's singleton, we could provide optimized
    -- instances of Eq and Ord, but they wouldn't quite be correct
    -- since someone may break the type system (e.g., with
    -- 'unsafeCoerce').


-- | Given a proof that a value has type @a@, return the value.
the :: OfType x a -> a
the (OfType a) = a
{-# INLINE the #-}


instance (IsOfType x a, Eq a, Read a) => Read (OfType x a) where
    readsPrec p str = reifys id (,) (readsPrec p str)
    {-# INLINE readsPrec #-}


----------------------------------------------------------------
-- | Proof that some reification of @x@ exists (or could exist)
-- such that @x@ has type @a@.
--
-- > Exists a ~ (exists x. OfType x a)
--
newtype Exists a = Exists (forall r. (forall x. OfType x a -> r) -> r)
    -- N.B., the true existential is logically more powerful than
    -- its double-negation. However, that would require
    -- ExistentialQuantification, and we don't seem to need the
    -- extra power. But then again, the double-negation (as a
    -- newtype) requires rank-3 types...


-- | Eliminate the existential.
--
-- > (exists x. OfType x a) -> not (forall x. not (OfType x a))
--
runExists :: Exists a -> (forall x. OfType x a -> r) -> r
runExists (Exists x) = x
{-# INLINE runExists #-}


-- | Given (a reflection of) @x@, return proof that @x@ has type
-- @a@. If we unpack the 'Exists' type, then we see that this
-- function is just asserting the (possible) existence of a reification
-- of @x@.
exists :: a -> Exists a
exists x = Exists (\k -> k (OfType x))
{-# INLINE exists #-}


-- | A constructive axiom of choice. If you can prove that there
-- exists a value of type @a@ then by golly there is one!
choose :: Exists a -> a
choose x = runExists x the
{-# INLINE choose #-}


instance Monad Exists where
    return  = exists
    x >>= f = f (choose x)
    {-# INLINE return #-}
    {-# INLINE (>>=)  #-}

instance Read a => Read (Exists a) where
    readsPrec p str = [(exists x, rest) | (x,rest) <- readsPrec p str]
    {-# INLINE readsPrec #-}

instance Show a => Show (Exists a) where
    showsPrec p x = showsPrec p (choose x)
    {-# INLINE showsPrec #-}

instance Eq a => Eq (Exists a) where
    x == y = choose x == choose y
    x /= y = choose x /= choose y
    {-# INLINE (==) #-}
    {-# INLINE (/=) #-}

instance Ord a => Ord (Exists a) where
    compare x y = compare (choose x) (choose y)
    x <  y      = choose x <  choose y
    x <= y      = choose x <= choose y
    x >  y      = choose x >  choose y
    x >= y      = choose x >= choose y
    min x y     = exists (min (choose x) (choose y))
    max x y     = exists (max (choose x) (choose y))
    {-# INLINE compare #-}
    {-# INLINE (<)  #-}
    {-# INLINE (<=) #-}
    {-# INLINE (>)  #-}
    {-# INLINE (>=) #-}
    {-# INLINE min  #-}
    {-# INLINE max  #-}

----------------------------------------------------------------
class IsOfType x a where
    -- | Given (a proxy for) @x@, return proof that (a reflection
    -- of) @x@ has type @a@. The only way you can do this is to
    -- fabricate the reflection and hand it to 'exists'.
    reflect_ :: proxy x -> Exists a


-- | Given (a proxy for) @x@, return proof that (a reflection of)
-- @x@ has type @a@.
reflect :: forall a x. IsOfType x a => Proxy x -> OfType x a
reflect _ = OfType (choose (reflect_ (Proxy :: Proxy x)))
{-# INLINE reflect #-}


-- BUG: this is far too weak to be useful...
-- | Given proof that there exists some @y@ of type @a@, if @x==y@
-- then return proof that @x@ has type @a@.
reify :: forall a x. (Eq a, IsOfType x a) => Exists a -> Maybe (OfType x a)
reify y
    | choose y == the x = Just x
    | otherwise         = Nothing
    where
    x = reflect (Proxy :: Proxy x)
{-# INLINE reify #-}


-- TODO: generalize to Traversable.
-- BUG: this is far too weak to be useful...
-- | Given a lens, attempt to 'reify' everything under the lens.
reifys
    :: forall a x b c d. (Eq a, IsOfType x a)
    => (b -> (Exists a, c))
    -> (OfType x a -> c -> d)
    -> [b] -> [d]
reifys unpack pack = foldr step []
    where
    x = reflect (Proxy :: Proxy x)
    step b ds
        | choose y == the x = pack x c : ds
        | otherwise         = ds
        where
        (y,c) = unpack b
{-# INLINE reifys #-}


----------------------------------------------------------------
data LT_
data EQ_
data GT_

instance IsOfType LT_ Ordering where reflect_ _ = exists LT 
instance IsOfType EQ_ Ordering where reflect_ _ = exists EQ 
instance IsOfType GT_ Ordering where reflect_ _ = exists GT 


----------------------------------------------------------------
----------------------------------------------------------- fin.
