{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
{-# LANGUAGE RankNTypes
           , ScopedTypeVariables
           , MultiParamTypeClasses
           #-}

{-# LANGUAGE CPP #-}
#if __GLASGOW_HASKELL__ >= 701
-- N.B., Data.Proxy isn't "safe".
{-# LANGUAGE Trustworthy #-}
#endif
----------------------------------------------------------------
--                                                    2013.05.29
-- |
-- Module      :  Data.Reflection.OfType
-- Copyright   :  2012--2013 wren ng thornton,
--                2009--2012 Edward Kmett,
--                2012 Elliott Hird,
--                2004 Oleg Kiselyov and Chung-chieh Shan
-- License     :  BSD3
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  experimental
-- Portability :  semi-portable (rank-N, scoped tyvars, MPTCs)
--
-- A fork of @reflection-1.1.6@ for removing the fundep.
----------------------------------------------------------------
module Data.Reflection.OfType
    (
    -- * Reification of type signature annotations
      HasType
    , TypeFor
    , OfType()
    , the
    , proxyOfType
    , unproxyOfType
    -- * Coersion between reified values
    , Iso()
    , fwd
    , bwd
    , invert
    , iso
    -- * Existential hiding of reified values
    -- ** The existential monad
    , Exists()
    , exists
    , runExists
    , mapExists
    , bindExists
    -- ** The existential category
    , Coexists(..)
    , coexists
    , uncoexists
    , idExists
    , composeExists
    -- ** The inhabitation monad
    , Inhabited(..)
    , runInhabited
    , inhabit
    , choose
    , bindInhabited
    -- * Reflection
    , Reifies(..)
    , reflect
    , reflect'
    -- * Reification
    , Reflects(..)
    , reify
    -- reifyCPS
    -- * Testing
    -- | These properties should always be true.
    , prop_reflectionsAreReified
    , prop_reificationsAreReflected
    ) where

import Data.Proxy          (Proxy(Proxy))
import Control.Applicative (Applicative(..))

----------------------------------------------------------------
-- | A value of type @x\`HasType\`a@ is a proof of the fact that
-- @x@ has type @a@. This is an 'OfType' alias for supporting infix
-- use. /N.B.,/ infix use requires @TypeOperators@.
type HasType x a = OfType a x


-- | A value of type @a\`TypeFor\`x@ is a proof of the fact that
-- @a@ is a type for @x@. This is an 'OfType' alias for supporting
-- infix use. /N.B.,/ infix use requires @TypeOperators@.
type TypeFor a x = OfType a x


-- | Values of type @(OfType a x)@ are proofs that (the reflection
-- of) @x@ has type @a@. Of course there's an easy proof: the
-- reflection of @x@ as an actual value of type @a@; hence, this
-- is a singleton type whose only value is the reflection of @x@
-- at type @a@. If we had true dependent types, this would be:
--
-- > data OfType (a::*) :: a -> * where
-- >      OfType_ :: (x::a) -> OfType a x
--
-- There are two main ways to construct proofs: 'reify', and
-- 'reflect'. These correspond to the two ways of constructing an
-- association between the value-level and the type-level (from
-- values to types, and from types to values, respectively). A
-- secondary way to construct proofs is to use 'inhabit', however
-- this only provides access to the proof in a monadic context.
newtype OfType a x = OfType a
    deriving (Show, Eq, Ord)
    -- N.B., do not export the constructor; else this is equivalent
    -- to @Tagged x a@, which allows people to change the tag!
    --
    -- N.B., because it's singleton, we could provide optimized
    -- instances of Eq and Ord, but they wouldn't quite be correct
    -- since someone may break the type system (e.g., with
    -- 'unsafeCoerce').


-- | Given a proof that some value @x@ has type @a@, return the value.
the :: OfType a x -> a
the (OfType a) = a
{-# INLINE the #-}


-- | A proxy constructor; for convenience.
proxyOfType :: Proxy a -> Proxy x -> Proxy (OfType a x)
proxyOfType _ _ = Proxy
{-# INLINE proxyOfType #-}


-- TODO: should we offer the parts separately instead of in a tuple?
-- | A proxy destructor; for convenience.
unproxyOfType :: Proxy (OfType a x) -> (Proxy a, Proxy x)
unproxyOfType _ = (Proxy,Proxy)
{-# INLINE unproxyOfType #-}


----------------------------------------------------------------
-- We could generalize this to be indexed by @f@ instead of @OfType
-- a@, but then we'd have to expose the constructor in order to
-- have that extension be of any use...
-- | The types @x@ and @y@ are isomorphic as values of type @a@.
data Iso a x y = Iso
    {
    -- | The forward part of an isomorphism.
    --
    -- > fwd i . bwd i == id
    -- > bwd i . fwd i == id
      fwd :: OfType a x -> OfType a y

    -- | The backward part of an isomorphism.
    --
    -- > fwd i . bwd i == id
    -- > bwd i . fwd i == id
    , bwd :: OfType a y -> OfType a x
    }


-- | Invert the direction of the isomorphism.
--
-- > invert . invert == id
--
invert :: Iso a x y -> Iso a y x
invert (Iso f g) = Iso g f
{-# INLINE invert #-}


-- | If @x==y@ then return proof of that fact. The proof is quite
-- weak: we only prove @(OfType a x \<-\> OfType a y)@, whereas
-- we'd really like to prove @(OfType a x ~ OfType a y)@. However,
-- in order to implement that latter goal, you need to implement
-- true singleton types using a GADT; for an example of this, see:
--
--  * <http://typesandkinds.wordpress.com/2012/12/01/decidable-propositional-equality-in-haskell/>
--
-- /N.B.,/ even if you break the type system to fabricate invalid
-- proofs of @(OfType a x)@ or @(OfType a y)@, the result, if it
-- exists, will always be an isomorphism. Breaking the type system
-- only allows you to fabricate invalid isomorphisms.
iso :: Eq a => OfType a x -> OfType a y -> Maybe (Iso a x y)
iso x y
    | the x == the y = Just (Iso (OfType . the) (OfType . the))
    | otherwise      = Nothing
{-# INLINE iso #-}
infix 4 `iso`

{-
-- If we had dependent types for defining TypeOf then it'd be easy:
iso : forall {a} {x y}
    , (forall x0 y0 : a, {x0 = y0} + {x0 <> y0})
    -> OfType a x
    -> OfType a y
    -> {OfType a x = OfType a y} + {OfType a x <> OfType a y}
iso eq x0 y0 :=
    match eq x y with
    | left EQ =>
        left (OfType a x <> OfType a y)
            (eq_ind_r (fun x1:a => OfType a x1 = OfType a y)
                (eq_refl (OfType a y)) EQ)
    | right NE =>
        right (OfType a x = OfType a y)
            (fun E : OfType a x = OfType a y => NE (?1 a x y eq x0 y0 E))
       end
-- Of course, it's not so easy to fill that hole on the inequality side... But then, we don't offer any proof there for the Haskell @iso@ either
-}

----------------------------------------------------------------
-- | Proofs of the fact that there exists some type @a@ satisfying
-- the predicate @f@.
--
-- > Exists f = exists a. f a
--
-- This type essentially forms a monad, but the kind isn't quite
-- right for providing actual instances of 'Functor', 'Applicative',
-- 'Monad', etc. So instead, we just provide the functions which
-- would normally be provided by those classes.
newtype Exists f = Exists (forall r. (forall a. f a -> r) -> r)


-- | Hide the fact that @a@ is the particular type satisfying the
-- predicate @f@.
exists :: f a -> Exists f
exists x = Exists (\k -> k x)
{-# INLINE exists #-}


-- | Eliminate the existential. This is a proof of the fact that:
--
-- > (exists a. f a) ==> not (forall a. not (f a))
--
runExists :: Exists f -> (forall a. f a -> r) -> r
runExists (Exists f) = f
{-# INLINE runExists #-}


-- | Apply a natural transformation to the predicate.
mapExists :: (forall a. f a -> g a) -> Exists f -> Exists g
mapExists eta (Exists f) = f (exists . eta)
{-# INLINE mapExists #-}
-- A less eager version is @Exists(\k -> f (k . eta))@ which is not
-- strictly identical to the version above because it swaps the
-- @Exists$\k->@ and @f$\x->@ components.


-- | Bind for the 'Exists' monad. This is just a type-restricted
-- version of 'runExists'.
bindExists :: Exists f -> (forall a. f a -> Exists g) -> Exists g
bindExists (Exists f) g = f g
{-# INLINE bindExists #-}


----------------------------------------------------------------
-- | Existential quantification in a negative position. When @b ~
-- Exists g@, this is an alias for the morphisms in the Kleisli
-- category of the 'Exists' monad. Unfortunately, even with this
-- restriction, the kinds aren't quite right for giving a 'Category'
-- instance. So instead, we just provide the functions which would
-- normally be provided by that class.
newtype Coexists f b = Coexists { unCoexists :: forall a. f a -> b }


-- | A proof of the fact that:
--
-- > ((exists a. f a) -> b) ==> (forall a. (f a -> b))
--
-- When @b ~ Exists g@: map a @Hask@-morphism of 'Exists' into an
-- @Exists@-morphism; aka, the inverse of the Kleisli category's
-- extension operator (star operator).
coexists :: (Exists f -> b) -> Coexists f b
coexists g = Coexists (g . exists)
{-# INLINE coexists #-}


-- | A proof of the fact that:
--
-- > (forall a. (f a -> b)) ==> ((exists a. f a) -> b)
--
-- When @b ~ Exists g@: map the @Exists@-morphism into a @Hask@-morphism
-- of 'Exists'; aka, the Kleisli category's extension operator (star
-- operator); aka, apply an @Exists@-morphism. This is just @flip
-- bindExists@.
uncoexists :: Coexists f b -> Exists f -> b
uncoexists (Coexists g) (Exists f) = f g
{-# INLINE uncoexists #-}


-- | The identity @Exists@-morphisms.
idExists :: Coexists f (Exists f)
idExists = Coexists exists
{-# INLINE idExists #-}


-- | Compose @Exists@-morphisms.
composeExists
    :: Coexists g (Exists h)
    -> Coexists f (Exists g)
    -> Coexists f (Exists h)
composeExists h (Coexists g) = Coexists (uncoexists h . g)
{-# INLINE composeExists #-}


----------------------------------------------------------------
-- | Proof that some reification of @x@ exists (or could exist)
-- such that @x@ has type @a@.
--
-- > Inhabited a ~ (exists x. OfType a x)
--
-- We use a newtype in order to give type class instances. The
-- 'Read' and 'Show' instances are the most interesting. As a 'Monad'
-- this is essentially just a glorified identity monad; the real
-- magic happens when you use 'bindInhabited' in order to gain
-- access to the proof.
--
-- BUG: the current 'Read' and 'Show' instances just read\/show the
-- underlying type (i.e., @a@); they don't prepend the constructors.
newtype Inhabited a = Inhabited { fromInhabited :: Exists (OfType a) }


-- | A variant of 'runExists' to reduce newtype noise.
runInhabited :: Inhabited a -> (forall x. OfType a x -> r) -> r
runInhabited (Inhabited (Exists f)) k = f k
{-# INLINE runInhabited #-}


-- | Given (a reflection of) @x@, return proof that @x@ has type
-- @a@. That is, we assert (the possibility of) the existence of a
-- reification of @x@.
inhabit :: a -> Inhabited a
inhabit x = Inhabited (exists (OfType x))
{-# INLINE inhabit #-}


-- | A constructive axiom of choice. If you can prove that there
-- exists a value of type @a@ then by golly there is one!
--
-- > choose x = runInhabited x the
--
choose :: Inhabited a -> a
choose (Inhabited (Exists f)) = f the
{-# INLINE choose #-}


-- | A variant of 'bindExists' to reduce newtype noise. This is
-- strictly more powerful than the @(>>=)@ for 'Inhabited'. This
-- is just a type-restricted version of 'runInhabited'.
bindInhabited
    :: Inhabited a -> (forall x. OfType a x -> Inhabited b) -> Inhabited b
bindInhabited (Inhabited (Exists f)) g = f g
{-# INLINE bindInhabited #-}


instance Functor Inhabited where
    fmap f x = inhabit (f $ choose x)
    {-# INLINE fmap #-}

instance Applicative Inhabited where
    pure    = inhabit
    f <*> x = inhabit (choose f $ choose x)
    {-# INLINE pure  #-}
    {-# INLINE (<*>) #-}

instance Monad Inhabited where
    return  = inhabit
    x >>= f = f (choose x)
    {-# INLINE return #-}
    {-# INLINE (>>=)  #-}

instance Read a => Read (Inhabited a) where
    -- BUG: we should lex "Inhabited" etc
    readsPrec p s = [(inhabit x,s') | (x,s') <- readsPrec p s]
    {-# INLINE readsPrec #-}

instance Show a => Show (Inhabited a) where
    -- BUG: we should prepend "Inhabited" etc
    showsPrec p x = showsPrec p (choose x)
    {-# INLINE showsPrec #-}

instance Eq a => Eq (Inhabited a) where
    x == y = choose x == choose y
    x /= y = choose x /= choose y
    {-# INLINE (==) #-}
    {-# INLINE (/=) #-}

instance Ord a => Ord (Inhabited a) where
    compare x y = compare (choose x) (choose y)
    x <  y      = choose x <  choose y
    x <= y      = choose x <= choose y
    x >  y      = choose x >  choose y
    x >= y      = choose x >= choose y
    min x y     = inhabit (min (choose x) (choose y))
    max x y     = inhabit (max (choose x) (choose y))
    {-# INLINE compare #-}
    {-# INLINE (<)  #-}
    {-# INLINE (<=) #-}
    {-# INLINE (>)  #-}
    {-# INLINE (>=) #-}
    {-# INLINE min  #-}
    {-# INLINE max  #-}

----------------------------------------------------------------
-- | The type @x@ reifies (a value of) type @a@ just in case we can
-- reflect @x@ into a value of type @a@.
class Reifies x a where
    -- TODO: is this the type the most useful? or should we accept a @proxy(OfType a x)@ instead?
    -- | Given (a proxy for) @x@, return proof that (a reflection
    -- of) @x@ has type @a@. The only way you can do this is to
    -- fabricate the reflection and hand it to 'inhabit'.
    reflect_ :: proxy x -> Inhabited a


-- TODO: is this the type the most useful for the default? or is reflect' better?
-- | Given (a proxy for) @x@, return proof that (a reflection of)
-- @x@ has type @a@.
reflect :: Reifies x a => Proxy x -> OfType a x
reflect p = OfType (choose (reflect_ p))
{-# INLINE reflect #-}


-- TODO: better name...
-- | Given a proxy for proof that @x@ has type @a@, return the
-- actual proof. This is a variant of 'reflect' which is occasionally
-- useful for specifying the type @a@.
reflect' :: Reifies x a => Proxy (OfType a x) -> OfType a x
reflect' _ = reflect Proxy
{-# INLINE reflect' #-}


----------------------------------------------------------------
-- | The type @x@ reflects (a value of) type @a@ just in case some
-- value of type @a@ is reified as @x@.
class Reflects x a where
    -- | Given some @y@, if @y@ is the reflection of @x@ at type
    -- @a@, then return its proxy. The canonical instance is:
    --
    -- > reify_ y k
    -- >     | y == x    = Just (k Proxy)
    -- >     | otherwise = Nothing
    --
    reify_ :: a -> (Proxy x -> r) -> Maybe r


-- TODO: is this the type the most useful for the default? or would it be better to pass a @Proxy x@?
-- | Given some @y@, if @y@ is the reflection of @x@ at type @a@,
-- then return the proof that @x@ has type @a@. /N.B.,/ this function
-- relies on the type context for specifying @x@, which may result
-- in returning @Nothing@ when you don't want it to. In order to
-- specify @x@ explicitly, see 'reify''.
reify :: forall a x. Reflects x a => a -> Maybe (OfType a x)
reify x = reify_ x fakeReflect
    where
    -- HACK: Must float out in order to propegate the return @x@ to @reify_@
    fakeReflect :: Proxy x -> OfType a x
    fakeReflect _ = OfType x
{-# INLINE reify #-}

{-
-- BUG: how to do this so that @x@ isn't just a skolem variable? We don't want just a shorthand for @runInhabited . inhabit@...
-- | Given some @y@, assert the possibility that there exists a
-- type @x@ which reifies @y@.
reifyCPS :: forall a r. a -> (forall x. Reflects x a => OfType a x -> r) -> r
reifyCPS x k =
    case reify_ x fakeReflect of
    Nothing -> error "reifyCPS: the impossible happened"
    Just r  -> r
    where
    -- HACK: Must float out
    fakeReflect :: forall x. Reflects x a => Proxy x -> r
    fakeReflect _ = k (OfType x)
{-# INLINE reifyCPS #-}
-}


----------------------------------------------------------------
-- | Reflections can always be reified. The @Proxy a@ is just for
-- specifying the type @a@.
--
-- > reify . the . reflect == Just . reflect
--
prop_reflectionsAreReified
    :: (Reifies x a, Reflects x a, Eq a) => Proxy x -> Proxy a -> Bool
prop_reflectionsAreReified p q =
    let x = reflect' (proxyOfType q p)
    in  reify (the x) == Just x


-- | Reifications are reflected. Vacuously true when @x@ is not the
-- reification of the @a@ we're given.
--
-- > maybe True (reflect p ==) (reify x)
--
prop_reificationsAreReflected
    :: (Reifies x a, Reflects x a, Eq a) => Proxy x -> a -> Bool
prop_reificationsAreReflected p x =
    case reify x of
    Just x' -> x' == reflect p
    Nothing -> True

----------------------------------------------------------------
{-
-- To avoid needing to enable EmptyDataDecls whenever we check this
data LT_ = LT_ 
data EQ_ = EQ_ 
data GT_ = GT_ 

instance Reifies LT_ Ordering where reflect_ _ = inhabit LT 
instance Reifies EQ_ Ordering where reflect_ _ = inhabit EQ 
instance Reifies GT_ Ordering where reflect_ _ = inhabit GT 

instance Reflects LT_ Ordering where
    reify_ LT k = Just (k Proxy)
    reify_ _  _ = Nothing
instance Reflects EQ_ Ordering where
    reify_ EQ k = Just (k Proxy)
    reify_ _  _ = Nothing
instance Reflects GT_ Ordering where
    reify_ GT k = Just (k Proxy)
    reify_ _  _ = Nothing
-}

----------------------------------------------------------------
----------------------------------------------------------- fin.
