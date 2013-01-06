{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
{-# LANGUAGE RankNTypes
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
-- Portability :  semi-portable (rank-N, MPTCs, scoped tyvars)
--
-- A fork of @reflection-1.1.6@ for removing the fundep.
----------------------------------------------------------------
module Data.Reflection.OfType
    (
    -- * Reification of type signature annotations
      OfType(), the
    -- * Coersion between reified values
    , Iso(), fstIso, sndIso, iso
    -- * Existential hiding of reified values
    , Exists(), runExists, exists, choose
    -- * Reflection of reified values
    , IsOfType(reflect_), reflect
    -- * Reification of values
    , IsOfKind(reify_), reify
    -- * Testing
    -- | These properties should always be true.
    , prop_reifyTheReflection
    , prop_reflectTheReification
    ) where

import Data.Proxy          (Proxy(Proxy))
import Control.Applicative (Applicative(..))

----------------------------------------------------------------
-- | Values of type @x\`OfType\`a@ are proofs that (the reflection
-- of) @x@ has type @a@. Of course there's an easy proof: the
-- reflection of @x@ as an actual value of type @a@; hence, this
-- is a singleton type whose only value is the reflection of @x@
-- at type @a@. The name is chosen to support infix use. And, indeed,
-- you can use it infix (provided @TypeOperators@ is enabled).
--
-- If we had true dependent types, this would be:
--
-- > type OfType x a = TypeOf a x
-- >
-- > data TypeOf (a::*) :: a -> * where
-- >      TypeOf_ :: (x::a) -> TypeOf a x
--
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

{-
-- The 'Read' instance is only provided because we can. However,
-- note that it is exceptionally weak since you can only read things
-- you could've gotten from 'reflect' anyways, and it's more expensive
-- since we need to check that the read value is equal to @x@.

instance (IsOfType x a, Eq a, Read a) => Read (OfType x a) where
    readsPrec p str = reifys id (,) (readsPrec p str)
    {-# INLINE readsPrec #-}
-}


----------------------------------------------------------------
-- | The types @x@ and @y@ are isomorphic as reifications of @a@.
data Iso a x y = Iso
    {
    -- |
    -- > fstIso i . sndIso i == id
    -- > sndIso i . fstIso i == id
      fstIso :: OfType x a -> OfType y a
    -- |
    -- > fstIso i . sndIso i == id
    -- > sndIso i . fstIso i == id
    , sndIso :: OfType y a -> OfType x a
    }


-- | If @x==y@ then return proof of that fact. The proof is quite
-- weak: we only prove @(OfType x a \<-\> OfType y a)@, whereas
-- we'd really like to prove @(OfType x a ~ OfType y a)@. Of course,
-- it's worth noting that @OfType@ is not injective in the first
-- type argument (since there may be many reifications of the same
-- value), so our desired goal would not admit proving @x~y@ (which
-- would be unsound).
--
-- N.B., even if you break the type system to fabricate invalid
-- proofs of @(OfType x a)@ or @(OfType y a)@, the result (if it
-- exists) will always be an isomorphism. Breaking the type system
-- just means you can fabricate invalid isomorphisms.
iso :: Eq a => OfType x a -> OfType y a -> Maybe (Iso a x y)
iso x y
    | the x == the y = Just (Iso (OfType . the) (OfType . the))
    | otherwise      = Nothing
{-# INLINE iso #-}
infix 4 `iso`

{-
-- If we had dependent types for defining TypeOf then it'd be easy:
iso : forall {a} {x y}
    , (forall x0 y0 : a, {x0 = y0} + {x0 <> y0})
    -> TypeOf a x
    -> TypeOf a y
    -> {TypeOf a x = TypeOf a y} + {TypeOf a x <> TypeOf a y}
iso eq x0 y0 :=
    match eq x y with
    | left EQ =>
        left (TypeOf a x <> TypeOf a y)
            (eq_ind_r (fun x1:a => TypeOf a x1 = TypeOf a y)
                (eq_refl (TypeOf a y)) EQ)
    | right NE =>
        right (TypeOf a x = TypeOf a y)
            (fun E : TypeOf a x = TypeOf a y => NE (?1 a x y eq x0 y0 E))
       end
-- Of course, it's not so easy to fill that hole on the inequality side... But then, we don't offer any proof there for the Haskell @iso@ either
-}

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


-- | Eliminate the existential. This is a proof of the fact that:
--
-- > (exists x. OfType x a) -> not (forall x. not (OfType x a))
--
runExists :: Exists a -> (forall x. OfType x a -> r) -> r
runExists (Exists x) = x
{-# INLINE runExists #-}


-- | Given (a reflection of) @x@, return proof that @x@ has type
-- @a@. That is, we assert (the possibility of) the existence of a
-- reification of @x@.
exists :: a -> Exists a
exists x = Exists (\k -> k (OfType x))
{-# INLINE exists #-}


-- | A constructive axiom of choice. If you can prove that there
-- exists a value of type @a@ then by golly there is one!
--
-- > choose x = runExists x the
--
choose :: Exists a -> a
choose x = runExists x the
{-# INLINE choose #-}


instance Functor Exists where
    fmap f x = exists (f $ choose x)
    {-# INLINE fmap #-}

instance Applicative Exists where
    pure    = exists
    f <*> x = exists (choose f $ choose x)
    {-# INLINE pure  #-}
    {-# INLINE (<*>) #-}

instance Monad Exists where
    return  = exists
    x >>= f = f (choose x)
    {-# INLINE return #-}
    {-# INLINE (>>=)  #-}

instance Read a => Read (Exists a) where
    -- BUG: we should lex "Exists"
    readsPrec p s = [(exists x,s') | (x,s') <- readsPrec p s]
    {-# INLINE readsPrec #-}

instance Show a => Show (Exists a) where
    -- BUG: we should prepend "Exists"
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


----------------------------------------------------------------
class IsOfKind x a where
    -- | Given some @y@, if @y@ is the reflection of @x@ at type
    -- @a@, then return its proxy. The canonical instance is:
    --
    -- > reify_ y k
    -- >     | y == x    = Just (k Proxy)
    -- >     | otherwise = Nothing
    --
    reify_ :: a -> (Proxy x -> r) -> Maybe r


-- | Given some @y@, if @y@ is the reflection of @x@ at type @a@,
-- then return the proof that @x@ has type @a@.
reify :: forall a x. IsOfKind x a => a -> Maybe (OfType x a)
reify x = reify_ x fakeReflect
    where
    fakeReflect :: Proxy x -> OfType x a
    fakeReflect _ = OfType x
{-# INLINE reify #-}


prop_reifyTheReflection
    :: forall a x. (IsOfType x a, IsOfKind x a, Eq a)
    => Proxy x -> Proxy a -> Bool
prop_reifyTheReflection p _ =
    let x = reflect p :: OfType x a
    in  reify (the x) == Just x


prop_reflectTheReification
    :: (IsOfType x a, IsOfKind x a, Eq a) => Proxy x -> a -> Bool
prop_reflectTheReification p x =
    case reify x of
    Just x' -> x' == reflect p
    Nothing -> True

----------------------------------------------------------------
{-
-- To avoid needing to enable EmptyDataDecls whenever we check this
data LT_ = LT_ 
data EQ_ = EQ_ 
data GT_ = GT_ 

instance IsOfType LT_ Ordering where reflect_ _ = exists LT 
instance IsOfType EQ_ Ordering where reflect_ _ = exists EQ 
instance IsOfType GT_ Ordering where reflect_ _ = exists GT 

instance IsOfKind LT_ Ordering where
    reify_ LT k = Just (k Proxy)
    reify_ _  _ = Nothing
instance IsOfKind EQ_ Ordering where
    reify_ EQ k = Just (k Proxy)
    reify_ _  _ = Nothing
instance IsOfKind GT_ Ordering where
    reify_ GT k = Just (k Proxy)
    reify_ _  _ = Nothing
-}

----------------------------------------------------------------
----------------------------------------------------------- fin.
