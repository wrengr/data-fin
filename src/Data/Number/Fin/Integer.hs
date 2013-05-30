{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
{-# LANGUAGE ScopedTypeVariables
           , DeriveDataTypeable
           , MultiParamTypeClasses
           , FlexibleContexts
           , CPP
           , Rank2Types
           #-}

#if __GLASGOW_HASKELL__ >= 701
-- N.B., Data.Proxy and Test.QuickCheck aren't "safe".
{-# LANGUAGE Trustworthy #-}
#endif
----------------------------------------------------------------
--                                                    2013.05.29
-- |
-- Module      :  Data.Number.Fin.Integer
-- Copyright   :  2012--2013 wren ng thornton
-- License     :  BSD3
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  experimental
-- Portability :  non-portable
--
-- A newtype of 'Integer' for finite subsets of the natural numbers.
----------------------------------------------------------------
module Data.Number.Fin.Integer
    (
    -- * @Fin@, finite sets of natural numbers
      Fin()
    
    -- ** Showing types
    , showFinType
    , showsFinType
    
    -- ** Convenience functions
    , minBoundOf
    , maxBoundOf
    
    -- ** Introduction and elimination
    , toFin
    , toFinProxy
    , toFinCPS
    , fromFin
    
    -- ** Views and coersions
    -- *** Weakening and maximum views
    , weaken
    , weakenLE
    , weakenPlus
    , maxView
    , maxViewLE
    
    -- *** Widening and the predecessor view
    , widen
    , widenLE
    , widenPlus
    , predView
    
    -- *** The ordinal-sum functor
    , plus
    , unplus
    , fplus
    
    -- *** Face- and degeneracy-maps
    , thin
    , thick
    -- TODO: is there any way to get equality to work right?
    ) where

import qualified Prelude.SafeEnum as SE
import Data.Ix
import Data.Number.Fin.TyDecimal (Nat, Succ, Add, NatLE)
import Data.Typeable   (Typeable)
import Data.Proxy      (Proxy(Proxy))
import Data.Reflection (Reifies(reflect), reify)
import Control.Monad   (liftM)

import qualified Test.QuickCheck as QC
#if (MIN_VERSION_smallcheck(0,6,0))
import qualified Test.SmallCheck.Series as SC
#else
import qualified Test.SmallCheck as SC
#endif
import qualified Test.LazySmallCheck as LSC

----------------------------------------------------------------
----------------------------------------------------------------
-- | A finite set of integers @Fin n = { i :: Integer | 0 <= i < n }@
-- with the usual ordering. This is typed as if using the standard
-- GADT presentation of @Fin n@, however it is actually implemented
-- by a plain 'Integer'.
--
-- If you care more about performance than mathematical accuracy,
-- see "Data.Number.Fin.Int32" for an alternative implementation
-- as a newtype of 'Int32'. Note, however, that doing so makes it
-- harder to reason about code since it introduces many corner
-- cases.
newtype Fin n = Fin Integer
    deriving Typeable
    -- WART: to give additional constraints (e.g., Nat n) on derived
    -- instances (e.g., Show, Eq, Ord), we need to specify the
    -- constraints on the data type declaration; however, giving of
    -- data-type constraints is deprecated and will be removed from
    -- the language...

{-
-- Some fusion rules for treating newtypes like 'id', or as close
-- as we can. We only have these fire in the last stage so that
-- they don't inhibit the usual list-fusion rules. Hopefully there's
-- nothing important which is defined to not fire at [0].
--
-- TODO: add other laws regarding 'id'
{-# RULES
"map Fin"      [0]  map   Fin = unsafeCoerce
"fmap Fin"     [0]  fmap  Fin = unsafeCoerce
"liftM Fin"    [0]  liftM Fin = unsafeCoerce
"liftA Fin"    [0]  liftA Fin = unsafeCoerce
    #-}
-}

{- TODO:
-- also: <http://paczesiowa.blogspot.com/2010/01/pure-extensible-exceptions-and-self.html>

-- | An error for attempts to evaluate an undefined value which is
-- passed around as a type token. The string should give the source
-- where the token was generated, or some other helpful information
-- for tracking the problem down.
data EvaluatedTypeTokenException = EvaluatedTypeTokenException String
    deriving (Typeable, Show)

instance Exception EvaluatedTypeTokenException

-- | Construct a type token with the given message.
__ :: String -> a
__ here = throw (EvaluatedTypeTokenException here)


-- TODO: use Control.Exception.assert instead?
data FinException = FinOOB (Fin n)
    deriving (Typeable)

instance Show FinException where
    show (FinOOB x) =
        "Value "++show x++" out of bounds for "++showFinType x

instance Exception FinException
-}


-- | Often, we don't want to use the @Fin n@ as a proxy, since that
-- would introduce spurious data dependencies. This function ignores
-- its argument (other than for type propagation) so, hopefully,
-- via massive inlining this function will avoid that spurious
-- dependency. Hopefully...
--
-- Also, this lets us minimize the use of @-XScopedTypeVariables@
-- which makes the Haddocks ugly. And so it lets us avoid the hacks
-- to hide our use of @-XScopedTypeVariables@.
--
-- TODO: is this enough to ensure reflection is/can-be done at compile-time?
-- TODO: is there any way to tell GHC that this function should /never/ appear in the output of compilation?
fin2proxy :: Nat n => fin n -> Proxy n
fin2proxy _ = Proxy
{-# INLINE fin2proxy #-}


----------------------------------------------------------------
-- HACK: Not derived, just so we can add the @Nat n@ constraint...
instance Nat n => Show (Fin n) where
    showsPrec d (Fin i) =
        showParen (d > 10) $ ("Fin "++) . shows i


-- | Like 'show', except it shows the type itself instead of the
-- value.
showFinType :: Nat n => Fin n -> String
showFinType x = showsFinType x []
{-# INLINE showFinType #-}
-- Should never fire, due to inlining
{- RULES
"showFinType/++"  forall x s. showFinType x ++ s = showsFinType x s
    -}


-- | Like 'shows', except it shows the type itself instead of the
-- value.
showsFinType :: Nat n => Fin n -> ShowS
showsFinType x = ("Fin "++) . shows (reflect (fin2proxy x))
{-# INLINE [0] showsFinType #-}
-- TODO: Is [0] the best level to start inlining showsFinType?
{-# RULES
"showsFinType/++"  forall x s1 s2.
    showsFinType x s1 ++ s2 = showsFinType x (s1 ++ s2)
    #-}

-- TODO: showsPrecFinType?

----------------------------------------------------------------
-- N.B., we cannot derive Read, since that would inject invalid numbers!
instance Nat n => Read (Fin n) where
    readsPrec d =
        readParen (d > 10) $ \s0 -> do
            ("Fin", s1) <- lex s0
            (i,     s2) <- readsPrec 11 s1
            maybe [] (\n -> [(n,s2)]) (toFin i)

----------------------------------------------------------------
-- HACK: Not derived, just so we can add the @Nat n@ constraint...
instance Nat n => Eq (Fin n) where
    Fin i == Fin j  =  i == j
    Fin i /= Fin j  =  i /= j
    {-# INLINE (==) #-}
    {-# INLINE (/=) #-}

----------------------------------------------------------------
-- HACK: Not derived, just so we can add the @Nat n@ constraint...
instance Nat n => Ord (Fin n) where
    Fin i <  Fin j          = i <  j
    Fin i <= Fin j          = i <= j
    Fin i >  Fin j          = i >  j
    Fin i >= Fin j          = i >= j
    compare (Fin i) (Fin j) = compare i j
    min     (Fin i) (Fin j) = Fin (min i j)
    max     (Fin i) (Fin j) = Fin (max i j)
    {-# INLINE (<)     #-}
    {-# INLINE (<=)    #-}
    {-# INLINE (>)     #-}
    {-# INLINE (>=)    #-}
    {-# INLINE compare #-}
    {-# INLINE min     #-}
    {-# INLINE max     #-}

----------------------------------------------------------------
instance Nat n => Bounded (Fin n) where
    minBound = Fin 0
    maxBound = Fin (reflect (Proxy :: Proxy n) - 1)
    {-# INLINE minBound #-}
    {-# INLINE maxBound #-}


-- | Return the 'minBound' of @Fin n@ as a plain integer. This is
-- always zero, but is provided for symmetry with 'maxBoundOf'.
minBoundOf :: Nat n => Fin n -> Integer
minBoundOf _ = 0
{-# INLINE minBoundOf #-}


-- | Return the 'maxBound' of @Fin n@ as a plain integer. This is
-- always @n-1@, but it's helpful because you may not know what
-- @n@ is at the time.
maxBoundOf :: Nat n => Fin n -> Integer
maxBoundOf x = reflect (fin2proxy x) - 1
{-# INLINE maxBoundOf #-}


----------------------------------------------------------------
-- N.B., we cannot derive Enum, since that would inject invalid numbers!
-- N.B., we're using partial functions, because H98 requires it!
instance Nat n => Enum (Fin n) where
    succ x =
        case SE.succ x of
        Just y  -> y
        Nothing -> _succ_maxBound "Fin" -- cf, @GHC.Word.succError@
    {-# INLINE succ #-}
    
    pred x =
        case SE.pred x of
        Just y  -> y
        Nothing -> _pred_minBound "Fin" -- cf, @GHC.Word.predError@
    {-# INLINE pred #-}
    
    toEnum i =
        case SE.toEnum i of
        Just y  -> y
        Nothing -> _toEnum_OOR "Fin" -- cf, @GHC.Word.toEnumError@
    {-# INLINE toEnum #-}
    
    fromEnum = fromInteger . fromFin
    {-# INLINE fromEnum #-}
    
    -- Hopefully list fusion will get rid of the map, and preserve
    -- the fusion tricks in GHC.Enum...
    enumFrom     x@(Fin i)        = map Fin (enumFromTo i (maxBoundOf x))
    enumFromThen x@(Fin i) (Fin j)
        | j >= i                  = map Fin (enumFromThenTo i j (maxBoundOf x))
        | otherwise               = map Fin (enumFromThenTo i j (minBoundOf x))
    enumFromTo     (Fin i)         (Fin k) = map Fin (enumFromTo i k)
    enumFromThenTo (Fin i) (Fin j) (Fin k) = map Fin (enumFromThenTo i j k)
    {-# INLINE enumFrom #-}
    {-# INLINE enumFromThen #-}
    {-# INLINE enumFromTo #-}
    {-# INLINE enumFromThenTo #-}

{-
_pred_succ :: Nat n => Fin n -> Fin n
_pred_succ x = if x == maxBound then _succ_maxBound "Fin" else x
{-# INLINE _pred_succ #-}

_succ_pred :: Nat n => Fin n -> Fin n
_succ_pred x = if x == minBound then _pred_minBound "Fin" else x
{-# INLINE _succ_pred #-}

-- BUG: how can we introduce the (Nat n) constraint? Floating out the RHSs to give them signatures doesn't help.
{-# RULES
"pred (succ x) :: Fin n"         forall x. pred (succ x) = _pred_succ x
"pred . succ :: Fin n -> Fin n"            pred . succ   = _pred_succ

"succ (pred x) :: Fin n"         forall x. succ (pred x) = _succ_pred x
"succ . pred :: Fin n -> Fin n"            succ . pred   = _succ_pred
    #-}
-}

instance Nat n => SE.UpwardEnum (Fin n) where
    succ x@(Fin i)
        | x < maxBound = Just $! Fin (i + 1)
        | otherwise    = Nothing
    succeeds   = (>)
    enumFrom   = enumFrom
    enumFromTo = enumFromTo
    {-# INLINE succ #-}
    {-# INLINE succeeds #-}
    {-# INLINE enumFrom #-}
    {-# INLINE enumFromTo #-}

instance Nat n => SE.DownwardEnum (Fin n) where
    pred (Fin i)
        | 0 < i     = Just $! Fin (i - 1)
        | otherwise = Nothing
    precedes = (<)
    enumDownFrom   (Fin i)         = map Fin (enumFromThenTo i (i-1) 0)
    enumDownFromTo (Fin i) (Fin k) = map Fin (enumFromThenTo i (i-1) (max 0 k))
    {-# INLINE pred #-}
    {-# INLINE precedes #-}
    {-# INLINE enumDownFrom #-}
    {-# INLINE enumDownFromTo #-}
    
instance Nat n => SE.Enum (Fin n) where
    toEnum i
        | 0 <= j && j <= maxBoundOf x = Just x
        | otherwise                   = Nothing
        where
        j = toInteger i
        x = Fin j :: Fin n
    fromEnum x     = Just $! (fromInteger . fromFin) x
    enumFromThen   = enumFromThen
    enumFromThenTo = enumFromThenTo
    {-# INLINE toEnum #-}
    {-# INLINE fromEnum #-}
    {-# INLINE enumFromThen #-}
    {-# INLINE enumFromThenTo #-}


-- TODO: can we trust the validity of the input arguments?
instance Nat n => Ix (Fin n) where
    index     (Fin i, Fin j) (Fin k) = index     (i,j) k
    range     (Fin i, Fin j)         = map Fin (range (i,j))
    inRange   (Fin i, Fin j) (Fin k) = inRange   (i,j) k
    rangeSize (Fin i, Fin j)         = rangeSize (i,j)


----------------------------------------------------------------
-- TODO: define Num, Real, Integral? (N.B., Can't derive them safely.)


----------------------------------------------------------------
-- TODO: why was the checking stuff done using exceptions instead of Maybe?
-- TODO: can we successfully ensure that invalid values can *never* be constructed?


-- | A version of 'const' which checks that the second argument is
-- in fact valid for its type before returning the first argument.
-- Throws an exception if the @Fin n@ is invalid. The name and
-- argument ordering are indended for infix use.
checking :: Nat n => a -> Fin n -> a
checking a x
    | minBound <= x && x <= maxBound = a
    | otherwise                      = _checking_OOR x
{-# INLINE checking #-}


-- TODO: use extensible-exceptions instead of 'error'
_checking_OOR :: Nat n => Fin n -> a
_checking_OOR x = error
    . ("The value "++)
    . shows x
    . (" is out of bounds for "++)
    . showsFinType x
    $ ". This is a library error; contact the maintainer."


-- | Extract the value of a @Fin n@.
--
-- /N.B.,/ if somehow the @Fin n@ value was constructed invalidly,
-- then this function will throw an exception. However, this should
-- /never/ happen. If it does, contact the maintainer since this
-- indicates a bug\/insecurity in this library.
fromFin :: Nat n => Fin n -> Integer
fromFin x@(Fin i) = i `checking` x
{-# INLINE fromFin #-}


-- | Safely embed a number into @Fin n@. Use of this function will
-- generally require an explicit type signature in order to know
-- which @n@ to use.
toFin :: Nat n => Integer -> Maybe (Fin n)
toFin = toFin_
    where
    -- HACK: Hiding the use of -XScopedTypeVariables from Haddock
    -- TODO: why is the choice of @n@ ambiguous?
    toFin_ :: forall n. Nat n => Integer -> Maybe (Fin n)
    toFin_ i
        | 0 <= i && i <= maxBoundOf x = Just x
        | otherwise                   = Nothing
        where
        x = Fin i :: Fin n
    {-# INLINE toFin_ #-}
{-# INLINE toFin #-}

-- TODO: RULES for toFin.fromFin and fromFin.toFin


-- | Safely embed a number into @Fin n@. This variant of 'toFin'
-- uses a proxy to avoid the need for type signatures.
toFinProxy :: Nat n => Proxy n -> Integer -> Maybe (Fin n)
toFinProxy _ = toFin
{-# INLINE toFinProxy #-}


-- | Safely embed integers into @Fin n@, where @n@ is the first
-- argument. We use rank-2 polymorphism to render the type-level
-- @n@ existentially quantified, thereby hiding the dependent type
-- from the compiler. However, @n@ will in fact be a skolem, so we
-- can't provide the continuation with proof that @Nat n@ ---
-- unfortunately, rendering this function of little use.
--
-- > toFinCPS n k i
-- >     | 0 <= i && i < n  = Just (k i)  -- morally speaking...
-- >     | otherwise        = Nothing
--
toFinCPS :: Integer -> (forall n. Reifies n Integer => Fin n -> r) -> Integer -> Maybe r
toFinCPS n k i
    | 0 <= i && i < n = Just (reify n $ \(_ :: Proxy n) -> k (Fin i :: Fin n))
    | otherwise       = Nothing
{-# INLINE toFinCPS #-}
-- BUG: can't use @Nat n@ because: Could not deduce (Nat_ n) from the context (Reifies n Integer)
-- TODO: how can we get Data.Number.Fin.TyDecimal.reifyNat to work?


----------------------------------------------------------------
instance Nat n => QC.Arbitrary (Fin n) where
    shrink = tail . SE.enumDownFrom
    arbitrary
        | x >= 0    = Fin `liftM` QC.choose (0,x)
        | otherwise =
            -- BUG: there's no way to say it's impossible...
            error . ("Arbitrary.arbitrary{"++)
                  . showsFinType (__ :: Fin n)
                  $ "}: this type is empty"
            -- TODO: use extensible-exceptions instead of 'error'
        where
        x = maxBoundOf (__ :: Fin n)
        


instance Nat n => QC.CoArbitrary (Fin n) where
    coarbitrary (Fin n) = QC.variant n


instance Nat n => SC.Serial (Fin n) where
    series d
        | d < 0     = [] -- paranoia.
        | otherwise =
            case toFin (toInteger d) of
            Nothing -> enumFromTo minBound maxBound
            Just n  -> enumFromTo minBound n
    
    coseries rs d =
        [ \(Fin i) ->
            if i > 0
            then let j = Fin (i-1) :: Fin n
                in f j `checking` j -- more paranoia; in case n==0 or i>n
            else z
        | z <- SC.alts0 rs d
        , f <- SC.alts1 rs d
        ]

instance Nat n => LSC.Serial (Fin n) where
    series = LSC.drawnFrom . SC.series


----------------------------------------------------------------
-- TODO: do we care about <http://ncatlab.org/nlab/show/decalage>?


-- TODO: define @Surely a = Only a | Everything@ instead of reusing Maybe?
{- -- Agda's version:
data MaxView {n : Nat} : Fin (suc n) -> Set where
  theMax :                MaxView (fromNat n)
  notMax : (i : Fin n) -> MaxView (weaken i)

maxView : {n : Nat} (i : Fin (suc n)) -> MaxView i
maxView {zero}  zero = theMax
maxView {zero}  (suc ())
maxView {suc n} zero = notMax zero
maxView {suc n} (suc i) with maxView i
maxView {suc n} (suc .(fromNat n)) | theMax   = theMax
maxView {suc n} (suc .(weaken i))  | notMax i = notMax (suc i)
-}
-- | The maximum-element view. This strengthens the type by removing
-- the maximum element:
--
-- > maxView maxBound = Nothing
-- > maxView x        = Just x  -- morally speaking...
--
-- The opposite of this function is 'weaken'.
--
-- > maxView . weaken                == Just
-- > maybe maxBound weaken . maxView == id
--
maxView :: Succ m n => Fin n -> Maybe (Fin m)
-- BUG: Could not deduce (NatLE m n) from the context (Succ m n)
maxView = maxView_
    where
    -- HACK: Hiding the use of -XScopedTypeVariables from Haddock
    -- TODO: why is the choice of @n@ ambiguous? Even using @y<=maxBound@ we still need the signature on @y@...
    maxView_ :: forall m n. Succ m n => Fin n -> Maybe (Fin m)
    maxView_ (Fin i)
        | i <= maxBoundOf y = Just y
        | otherwise         = Nothing
        where
        y = Fin i :: Fin m
    {-# INLINE maxView_ #-}
{-# INLINE maxView #-}


-- | A variant of 'maxView' which allows strengthening the type by
-- multiple steps. Use of this function will generally require an
-- explicit type signature in order to know which @m@ to use.
--
-- The opposite of this function is 'weakenLE'. When the choice of
-- @m@ and @n@ is held constant, we have that:
--
-- > maxViewLE . weakenLE      == Just
-- > fmap weakenLE . maxViewLE == (\i -> if i < m then Just i else Nothing)
--
maxViewLE :: NatLE m n => Fin n -> Maybe (Fin m)
maxViewLE = maxViewLE_
    where
    -- HACK: Hiding the use of -XScopedTypeVariables from Haddock
    maxViewLE_ :: forall m n. NatLE m n => Fin n -> Maybe (Fin m)
    maxViewLE_ (Fin i)
        | i <= maxBoundOf y = Just y
        | otherwise         = Nothing
        where
        y = Fin i :: Fin m
    {-# INLINE maxViewLE_ #-}
{-# INLINE maxViewLE #-}


-- TODO: maxViewPlus?


-- This type-restricted version is a~la Agda.
-- | Embed a finite domain into the next larger one, keeping the
-- same position relative to 'minBound'. That is,
--
-- > fromFin (weaken x) == fromFin x
--
-- The opposite of this function is 'maxView'.
--
-- > maxView . weaken                == Just
-- > maybe maxBound weaken . maxView == id
--
weaken :: Succ m n => Fin m -> Fin n
-- BUG: Could not deduce (NatLE m n) from the context (Succ m n)
weaken (Fin i) = Fin i
{-# INLINE weaken #-}


-- | A variant of 'weaken' which allows weakening the type by
-- multiple steps. Use of this function will generally require an
-- explicit type signature in order to know which @n@ to use.
--
-- The opposite of this function is 'maxViewLE'. When the choice
-- of @m@ and @n@ is held constant, we have that:
--
-- > maxViewLE . weakenLE      == Just
-- > fmap weakenLE . maxViewLE == (\i -> if i < m then Just i else Nothing)
--
weakenLE :: NatLE m n => Fin m -> Fin n
weakenLE (Fin i) = Fin i
{-# INLINE weakenLE #-}


----------------------------------------------------------------
-- | The predecessor view. This strengthens the type by shifting
-- everything down by one:
--
-- > predView 0 = Nothing
-- > predView x = Just (x-1)  -- morally speaking...
--
-- The opposite of this function is 'widen'.
--
-- > predView . widen         == Just
-- > maybe 0 widen . predView == id
--
predView :: Succ m n => Fin n -> Maybe (Fin m)
predView (Fin i)
    | i <= 0    = Nothing
    | otherwise = Just $! Fin (i-1)
{-# INLINE predView #-}


-- TODO: predViewLE? predViewPlus?


-- | Embed a finite domain into the next larger one, keeping the
-- same position relative to 'maxBound'. That is, we shift everything
-- up by one:
--
-- > fromFin (widen x) == 1 + fromFin x
--
-- The opposite of this function is 'predView'.
--
-- > predView . widen         == Just
-- > maybe 0 widen . predView == id
--
widen :: Succ m n => Fin m -> Fin n
widen (Fin i) = Fin (i+1)
{-# INLINE widen #-}


-- | Embed a finite domain into any larger one, keeping the same
-- position relative to 'maxBound'. That is,
--
-- > maxBoundOf y - fromFin y == maxBoundOf x - fromFin x
-- >     where y = widenLE x
--
-- Use of this function will generally require an explicit type
-- signature in order to know which @n@ to use.
widenLE :: NatLE m n => Fin m -> Fin n
widenLE x@(Fin i) = y
    where
    y = Fin (maxBoundOf y - maxBoundOf x + i)
{-# INLINE widenLE #-}


----------------------------------------------------------------
-- BUG: Could not deduce (NatLE m o) from the context (Add m n o)
-- | A type-signature variant of 'weakenLE' because we cannot
-- automatically deduce that @Add m n o ==> NatLE m o@. This is the
-- left half of 'plus'.
weakenPlus :: Add m n o => Fin m -> Fin o
weakenPlus (Fin i) = Fin i
{-# INLINE weakenPlus #-}


-- BUG: Could not deduce (NatLE n o) from the context (Add m n o)
-- | A type-signature variant of 'widenLE' because we cannot
-- automatically deduce that @Add m n o ==> NatLE n o@. This is the
-- right half of 'plus'.
widenPlus :: Add m n o => Fin n -> Fin o
widenPlus = widenPlus_
    where
    -- HACK: Hiding the use of -XScopedTypeVariables from Haddock
    widenPlus_ :: forall m n o. Add m n o => Fin n -> Fin o
    widenPlus_ y = Fin (maxBoundOf (__::Fin m) + fromFin y)
    {-# INLINE widenPlus_ #-}
{-# INLINE widenPlus #-}


-- BUG: Could not deduce (NatLE m o, NatLE n o) from the context (Add m n o)
-- | The ordinal-sum functor, on objects. This internalizes the
-- disjoint union, mapping @Fin m + Fin n@ into @Fin(m+n)@ by
-- placing the image of the summands next to one another in the
-- codomain, thereby preserving the structure of both summands.
plus :: Add m n o => Either (Fin m) (Fin n) -> Fin o
plus = either weakenPlus widenPlus
{-# INLINE plus #-}


-- | The inverse of 'plus'.
unplus :: Add m n o => Fin o -> Either (Fin m) (Fin n)
unplus = unplus_
    where
    -- HACK: Hiding the use of -XScopedTypeVariables from Haddock
    unplus_ :: forall m n o. Add m n o => Fin o -> Either (Fin m) (Fin n)
    unplus_ (Fin i)
        | i <= x    = Left  $! Fin i
        | otherwise = Right $! Fin (i-x)
        where
        x = maxBoundOf (__ :: Fin m)
    {-# INLINE unplus_ #-}
{-# INLINE unplus #-}


-- BUG: Could not deduce (NatLE m o, NatLE n o) from the context (Add m n o)
-- BUG: Ditto for (Add m' n' o')
-- | The ordinal-sum functor, on morphisms. If we view the maps as
-- bipartite graphs, then the new map is the result of placing the
-- left and right maps next to one another. This is similar to
-- @(+++)@ from "Control.Arrow".
fplus :: (Add m n o, Add m' n' o')
       => (Fin m -> Fin m') -- ^ The left morphism
       -> (Fin n -> Fin n') -- ^ The right morphism
       -> (Fin o -> Fin o') -- ^
fplus = fplus_
    where
    -- HACK: Hiding the use of -XScopedTypeVariables from Haddock
    fplus_ :: forall m n o m' n' o'. (Add m n o, Add m' n' o')
           => (Fin m -> Fin m') -> (Fin n -> Fin n') -> Fin o -> Fin o'
    fplus_ f g (Fin i)
        | i <= x    = weakenPlus (f $! Fin i)
        | otherwise = widenPlus  (g $! Fin (i-x))
        where
        x = maxBoundOf (__ :: Fin m)
    {-# INLINE fplus_ #-}
{-# INLINE fplus #-}


-- TODO: (Fin m, Fin n) <-> Fin (Times m n)

----------------------------------------------------------------
{- -- Agda's version:
thin : {n : Nat} -> Fin (suc n) -> Fin n -> Fin (suc n)
thin zero    j       = suc j
thin (suc i) zero    = zero
thin (suc i) (suc j) = suc (thin i j)
-}
-- | The \"face maps\" for @Fin@ viewed as the standard simplices
-- (aka: the thinning view). Traditionally spelled with delta or
-- epsilon. For each @i@, it is the unique injective monotonic map
-- that skips @i@. That is,
--
-- > thin i = (\j -> if j < i then j else succ j)  -- morally speaking...
--
-- Which has the important universal property that:
--
-- > thin i j /= i
--
thin :: Succ m n => Fin n -> Fin m -> Fin n
thin i j
    | weaken j < i = weaken j
    | otherwise    = succ (weaken j)
{-# INLINE thin #-}


-- | The \"degeneracy maps\" for @Fin@ viewed as the standard
-- simplices. Traditionally spelled with sigma or eta. For each
-- @i@, it is the unique surjective monotonic map that covers @i@
-- twice. That is,
--
-- > thick i = (\j -> if j <= i then j else pred j)  -- morally speaking...
--
-- Which has the important universal property that:
--
-- > thick i (i+1) == i
--
thick :: Succ m n => Fin m -> Fin n -> Fin m
thick i j =
    case maxView (if j <= weaken i then j else pred j) of
    Just j' -> j'
    Nothing -> _thick_impossible
{-# INLINE thick #-}



{-
-- ueh? this is just another way to test for n==0; why bother with this? The only possible use I could see is to say, hey I have an actual value of Fin n, therefore n can't be zero... but then if you had a purported value of Fin n and that wasn't the case, then you'd have a contradiction to work with, ne?
-- The non zero view, which is used for defining compare...
data NonEmptyView : {n : Nat} -> Fin n -> Set where
  ne : {n : Nat}{i : Fin (suc n)} -> NonEmptyView i

nonEmpty : {n : Nat}(i : Fin n) -> NonEmptyView i
nonEmpty zero    = ne
nonEmpty (suc _) = ne


data EqView : {n : Nat} -> Fin n -> Fin n -> Set where
  equal    : {n : Nat}{i : Fin n} -> EqView i i
  notequal : {n : Nat}{i : Fin (suc n)}(j : Fin n) -> EqView i (thin i j)

compare : {n : Nat}(i j : Fin n) -> EqView i j
compare zero    zero                           = equal
compare zero    (suc j)                        = notequal j
compare (suc i) zero              with nonEmpty i
...                               | ne         = notequal zero
compare (suc i) (suc j)           with compare i j
compare (suc i) (suc .i)          | equal      = equal
compare (suc i) (suc .(thin i j)) | notequal j = notequal (suc j)
-}

----------------------------------------------------------------
----------------------------------------------------------------
-- Error messages

__ :: a
__ = error "Data.Number.Fin: attempted to evaluate type token"
{-# NOINLINE __ #-}
-- TODO: use extensible-exceptions instead of 'error'
-- TODO: use Proxy instead of these undefined values...

_thick_impossible :: a
_thick_impossible = error "Data.Number.Fin.thick: the impossible happened"
{-# NOINLINE _thick_impossible #-}
-- TODO: use extensible-exceptions instead of 'error'

_succ_maxBound :: String -> a
_succ_maxBound ty =
    error $ "Enum.succ{"++ty++"}: tried to take `succ' of maxBound"
{-# NOINLINE _succ_maxBound #-}
-- TODO: is there an extensible-exception for this?

_pred_minBound :: String -> a
_pred_minBound ty =
    error $ "Enum.pred{"++ty++"}: tried to take `pred' of minBound"
{-# NOINLINE _pred_minBound #-}
-- TODO: is there an extensible-exception for this?

_toEnum_OOR :: String -> a
_toEnum_OOR ty =
    error $ "Enum.toEnum{"++ty++"}: argument out of range"
{-# NOINLINE _toEnum_OOR #-}
-- TODO: is there an extensible-exception for this?

----------------------------------------------------------------
----------------------------------------------------------- fin.
