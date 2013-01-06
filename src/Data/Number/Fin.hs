{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
{-# LANGUAGE ScopedTypeVariables
           , GeneralizedNewtypeDeriving
           , DeriveDataTypeable
           , MultiParamTypeClasses
           , CPP
           , Rank2Types
           #-}
----------------------------------------------------------------
--                                                    2013.01.04
-- |
-- Module      :  Data.Number.Fin
-- Copyright   :  2012--2013 wren ng thornton
-- License     :  BSD3
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  experimental
-- Portability :  non-portable
--
-- A newtype of 'Int' for finite subsets of the natural numbers.
--
-- TODO: offer a newtype of 'Fin' as @IntMod@ which offers 'Num', and use @type-level@ for doing arithmetic at the type level (though that uses @syb@ and template haskell...)
----------------------------------------------------------------
module Data.Number.Fin
    (
    -- * @Fin@, finite sets of natural numbers
      Fin()
    , showFinType
    , showsFinType
    , toFin
    , toFinCPS
    , fromFin
    -- predView
    -- weaken
    , weakenLE
    -- widen
    , widenLE
    , minBoundOf
    , maxBoundOf
    -- ** Shorthands for some small numbers.
    , Zero
    , One
    , Two
    , Three
    , Four
    , Five
    , Six
    , Seven
    , Eight
    , Nine
    ) where

import qualified Prelude.SafeEnum as SE
import Data.Ix
import Data.Number.Fin.TyInteger
import Data.Typeable (Typeable)
import Control.Monad (liftM)
#ifdef __GLASGOW_HASKELL__
import GHC.Exts (build)
#endif

import qualified Test.QuickCheck as QC
#if (MIN_VERSION_smallcheck(0,6,0))
import qualified Test.SmallCheck.Series as SC
#else
import qualified Test.SmallCheck as SC
#endif
import qualified Test.LazySmallCheck as LSC

----------------------------------------------------------------
----------------------------------------------------------------

{-
-- TODO: make Fin a newtype family indexed by the representation type it's a newtype of (e.g., the version here would be @Fin Int n@). That way we could add a constraint to ReflectNum\/reflectNum (and hence 'toFin') to ensure correct behavior! Then we could adjust representation types with @coerce :: (LE n (MaxBound r), LE n (MaxBound r')) => Fin r n -> Fin r' n@. This would also work great with @Int `Mod` n@ for the modular arithmetic!

-- works in GHCi 7.6.1, the kind signature is required..., backticks *do* work
data family Fin r :: * -> *
newtype instance Fin Int n = FinInt Int

-- so does:
class ReifyNum r => ReflectNum r s where
    reflectNum :: s -> r
class ReifyNum r where
    type MaxBound r :: * -- maxBound+1 would be okay for the purposes of Fin (since we do -1); but it must be maxBound itself for ReflectNum
    type MinBound r :: *
    reifyNum :: r -> (forall s. ReflectNum r s => s -> w) -> w

class ReifyNum r => Finite r where
    data Fin r :: * -> *
    toFin   :: ReflectNum r n => r -> Maybe (Fin r n)
    fromFin :: ReflectNum r n => Fin r n -> r
instance Finite Int where
    newtype Fin Int n = FinInt Int
    type MaxBound Int = Positive (X2(X1(X4(X7(X4(X8(X3(X6(X4(X8 X_))))))))))
    toFin = Just . FinInt
    fromFin (FinInt i) = i

cf. ekmett's
-- > reify :: a -> (forall s. Reifies s a => Proxy s -> r) -> r
-- > class Reifies s a | s -> a where reflect :: proxy s -> a

Of course, that fundep means we'd need to add another wrapper around the type-level numbers in order to indicate their desired representation type... ugh. Though surely it's there for a reason... I guess we'll have to put MinBound and MaxBound somewhere else, where we're defining those representation type wrappers...

-- | Values of type @x `OfType` a@ are proofs that (the reflection
-- of) @x@ has type @a@. Of course there's an easy proof: the
-- reflection of @x@ as an actual value of type @a@; hence, this
-- is a singleton type whose only value is the reflection of @x@
-- at type @a@.
newtype OfType x a = OfType a
    -- N.B., do not export the constructor; else this is equivalent to @Tagged x a@, which allows people to change the tag!

kind TyInteger where
    type Positive :: TyUnsigned -> TyInteger
    type Negative :: TyUnsigned -> TyInteger

kind TyUnsigned where
    type X_ :: TyUnsigned
    type X0 :: TyUnsigned -> TyUnsigned
    type X1 :: TyUnsigned -> TyUnsigned
    type X2 :: TyUnsigned -> TyUnsigned
    type X3 :: TyUnsigned -> TyUnsigned
    type X4 :: TyUnsigned -> TyUnsigned
    type X5 :: TyUnsigned -> TyUnsigned
    type X6 :: TyUnsigned -> TyUnsigned
    type X7 :: TyUnsigned -> TyUnsigned
    type X8 :: TyUnsigned -> TyUnsigned
    type X9 :: TyUnsigned -> TyUnsigned

type family MinBound :: * -> TyInteger
type family MaxBound :: * -> TyInteger

instance
    ( LE s (MaxBound r)
    , LE Zero s
    , Reifies s XRepr
    , Num r
    ) => Reifies (Positive s `OfType` r) r
    where reflect _ = reflect (Proxy :: Proxy s) `applyXRepr` 0
instance
    ( LE (MinBound r) s
    , LE s Zero
    , Reifies s XRepr
    , Num r
    ) => Reifies (Negative s `OfType` r) r
    where reflect _ = negate (reflect (Proxy :: Proxy s) `applyXRepr` 0)

-- Ideally we'd like to just use @(r -> r)@ with a @Num r@ constraint on the instance, but that requires FlexibleInstances since the @r@ is duplicated. So then we could try @Endo r@, but that requires UndecidableInstances since it violates the coverage condition, apparently. Thus, we end up with this type. Alas, it will almost surely interfere with all the inlining necessary to monomorphize and linearize the actual code. So the question is, which is more expensive: interpreting an XRepr datatype at known fixed types, or this polymorphic interpretation-less approach?
newtype XRepr = XRepr (forall r. Num r => r -> r)

instance Monoid XRepr where
    mempty                    = XRepr id
    XRepr f `mappend` XRepr g = XRepr (f .! g)

XRepr f `applyXRepr` x = f $! x

-- BUG: this could still be screwed up if overlapping instances are allowed...
instance Reifies X_ XRepr where
    reflect _ = mempty
instance Reifies s XRepr => Reifies (X0 s) XRepr where
    reflect _ = reflect (Proxy :: Proxy s) <> XRepr (\n -> 0 + 10*n)
instance Reifies s XRepr => Reifies (X1 s) XRepr where
    reflect _ = reflect (Proxy :: Proxy s) <> XRepr (\n -> 1 + 10*n)
instance Reifies s XRepr => Reifies (X2 s) XRepr where
    reflect _ = reflect (Proxy :: Proxy s) <> XRepr (\n -> 2 + 10*n)
instance Reifies s XRepr => Reifies (X3 s) XRepr where
    reflect _ = reflect (Proxy :: Proxy s) <> XRepr (\n -> 3 + 10*n)
instance Reifies s XRepr => Reifies (X4 s) XRepr where
    reflect _ = reflect (Proxy :: Proxy s) <> XRepr (\n -> 4 + 10*n)
instance Reifies s XRepr => Reifies (X5 s) XRepr where
    reflect _ = reflect (Proxy :: Proxy s) <> XRepr (\n -> 5 + 10*n)
instance Reifies s XRepr => Reifies (X6 s) XRepr where
    reflect _ = reflect (Proxy :: Proxy s) <> XRepr (\n -> 6 + 10*n)
instance Reifies s XRepr => Reifies (X7 s) XRepr where
    reflect _ = reflect (Proxy :: Proxy s) <> XRepr (\n -> 7 + 10*n)
instance Reifies s XRepr => Reifies (X8 s) XRepr where
    reflect _ = reflect (Proxy :: Proxy s) <> XRepr (\n -> 8 + 10*n)
instance Reifies s XRepr => Reifies (X9 s) XRepr where
    reflect _ = reflect (Proxy :: Proxy s) <> XRepr (\n -> 9 + 10*n)
-}

----------------------------------------------------------------
-- | A finite set of integers @Fin n = { i | 0 <= i < n }@ with the
-- usual ordering. This is typed as if using the standard GADT
-- presentation of @Fin n@, however it is actually implemented by
-- plain integers.
newtype Fin n = Fin Int
    deriving (Show, Eq, Ord, Typeable)
    -- BUG? derived instances don't get ReflectNum constraints...

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

-- TODO: don't re-use the LE class for this. Define a new class for one domain being smaller than another...
instance (ReflectNum m, ReflectNum n, LE m n) => LE (Fin m) (Fin n)

-- TODO: f :: Maybe (Fin n)          <-> Fin (Succ n) -- both obvious versions
    -- TODO: define @Surely a = Only a | Everything@ instead of reusing Maybe?
-- TODO: f :: Either (Fin m) (Fin n) <-> Fin (Plus m n)
-- TODO: f :: (Fin m, Fin n)         <-> Fin (Times m n)

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


-- | Like 'show', except it shows the type itself instead of the
-- value.
showFinType :: ReflectNum n => Fin n -> String
showFinType x = showsFinType x []
{-# INLINE showFinType #-}


-- N.B., we use @showsPrec 11@ rather than 'shows' to add parentheses
-- when @n@ is negative. And we use 'toInteger' just in case @n-1==maxBound@.
-- BUG: if @n-1 > maxBound@ we still get overflow to negatives...
-- | Like 'shows', except it shows the type itself instead of the
-- value.
showsFinType :: ReflectNum n => Fin n -> ShowS
showsFinType x = ("Fin "++) . showsPrec 11 (1 + toInteger (maxBoundOf x))
-- TODO: would inlining ensure compile-time reflection?
-- {-# INLINE showsFinType #-}


-- BUG: this only reads numeric literals, not ("Fin "++show n) and equivalent things...
instance ReflectNum n => Read (Fin n) where
#ifdef __GLASGOW_HASKELL__
    readsPrec p str = build (\cons nil ->
        let step (i,rest) xs = maybe xs (\x -> cons (x,rest) xs) (toFin i)
        in  foldr step nil (readsPrec p str))
#else
    readsPrec = (foldr step [] .) . readsPrec
        where
        step (i,rest) xs = maybe xs (\x -> (x,rest):xs) (toFin i)
#endif
{- -- TODO: this works, but how can we do fusion? or does it matter?
    readsPred d =
        -- The name shadowing is intentional
        readParen (d > 10) $ \s -> do
            ("Fin", s) <- lex s
            (i,     s) <- readsPrec 11 s
            maybe [] (\n -> [(n,s)]) (toFin i)
-}


----------------------------------------------------------------
instance ReflectNum n => Bounded (Fin n) where
    minBound = Fin 0
    {-# INLINE minBound #-}
    maxBound = Fin (reflectNum (__ :: n) - 1)
    {-# INLINE maxBound #-}


-- | Return the 'minBound' of @Fin n@ as a plain integer. This is
-- always zero, but is provided for symmetry with 'maxBoundOf'.
minBoundOf :: ReflectNum n => Fin n -> Int
minBoundOf _ = 0
{-# INLINE minBoundOf #-}


-- | Return the 'maxBound' of @Fin n@ as a plain integer. This is
-- always @n-1@, but it's helpful because you may not know what @n@
-- is at the time.
maxBoundOf :: ReflectNum n => Fin n -> Int
maxBoundOf x =
    case maxBound `asTypeOf` x of
    Fin i -> i
{-# INLINE maxBoundOf #-}


-- N.B., we cannot derive Enum, since that would inject invalid numbers!
-- N.B., we're using partial functions, because H98 requires it!
instance ReflectNum n => Enum (Fin n) where
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
    
    fromEnum = fromFin
    {-# INLINE fromEnum #-}
    
    {- Hopefully list fusion will get rid of the map, and preserve the fusion tricks in GHC.Enum -}
    enumFrom     x@(Fin i)  = map Fin (enumFromTo i (maxBoundOf x))
    {-# INLINE enumFrom #-}
    enumFromThen x@(Fin i) (Fin j)
        | j >= i            = map Fin (enumFromThenTo i j (maxBoundOf x))
        | otherwise         = map Fin (enumFromThenTo i j (minBoundOf x))
    {-# INLINE enumFromThen #-}
    enumFromTo     (Fin i)         (Fin k) = map Fin (enumFromTo i k)
    {-# INLINE enumFromTo #-}
    enumFromThenTo (Fin i) (Fin j) (Fin k) = map Fin (enumFromThenTo i j k)
    {-# INLINE enumFromThenTo #-}

{-
_pred_succ :: ReflectNum n => Fin n -> Fin n
_pred_succ x = if x == maxBound then _succ_maxBound "Fin" else x
{-# INLINE _pred_succ #-}

_succ_pred :: ReflectNum n => Fin n -> Fin n
_succ_pred x = if x == minBound then _pred_minBound "Fin" else x
{-# INLINE _succ_pred #-}

-- BUG: how can we introduce the (ReflectNum n) constraint? Floating out the RHSs to give them signatures doesn't help.
{-# RULES
"pred (succ x) :: Fin n"         forall x. pred (succ x) = _pred_succ x
"pred . succ :: Fin n -> Fin n"            pred . succ   = _pred_succ

"succ (pred x) :: Fin n"         forall x. succ (pred x) = _succ_pred x
"succ . pred :: Fin n -> Fin n"            succ . pred   = _succ_pred
    #-}
-}

instance ReflectNum n => SE.UpwardEnum (Fin n) where
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

instance ReflectNum n => SE.DownwardEnum (Fin n) where
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
    
instance ReflectNum n => SE.Enum (Fin n) where
    toEnum i
        | 0 <= i && i <= maxBoundOf x = Just x
        | otherwise                   = Nothing
        where
        x = Fin i :: Fin n
    fromEnum x     = Just $! fromFin x
    enumFromThen   = enumFromThen
    enumFromThenTo = enumFromThenTo
    {-# INLINE toEnum #-}
    {-# INLINE fromEnum #-}
    {-# INLINE enumFromThen #-}
    {-# INLINE enumFromThenTo #-}


-- TODO: predView :: Fin n -> Maybe (Fin (Pred n))
-- TODO: wtf? <http://ncatlab.org/nlab/show/decalage>


-- TODO: can we trust the validity of the input arguments?
instance ReflectNum n => Ix (Fin n) where
    index     (Fin i, Fin j) (Fin k) = index     (i,j) k
    range     (Fin i, Fin j)         = map Fin (range (i,j))
    inRange   (Fin i, Fin j) (Fin k) = inRange   (i,j) k
    rangeSize (Fin i, Fin j)         = rangeSize (i,j)


----------------------------------------------------------------
-- TODO: define Num, Real, Integral? (N.B., Can't derive them safely.)


----------------------------------------------------------------
-- TODO: why was the checking stuff done using exceptions instead of Maybe?
-- TODO: can we successfully ensure that invalid values can *never* be constructed?

-- | A version of 'id' which checks that the argument is in fact
-- valid for its type before returning it. Throws an exception if
-- the @Fin n@ is invalid.
check :: ReflectNum n => Fin n -> Fin n
check x = x `checking` x
{-# INLINE check #-}


-- | A version of 'const' which checks that the second argument is
-- in fact valid for its type before returning the first argument.
-- Throws an exception if the @Fin n@ is invalid. The name and
-- argument ordering are indended for infix use.
checking :: ReflectNum n => a -> Fin n -> a
checking a x
    | minBound <= x && x <= maxBound = a
    | otherwise                      = _checking_OOR x
{-# INLINE checking #-} 


-- TODO: use extensible-exceptions instead of 'error'
_checking_OOR :: ReflectNum n => Fin n -> a
_checking_OOR x = error
    . ("The value "++)
    . shows x 
    . (" is out of bounds for "++) 
    $ showFinType x


-- | Extract the value of a @Fin n@.
--
-- N.B., this function will throw an exception if, somehow, the
-- @Fin n@ value was constructed invalidly. However, this should
-- /never/ happen. If it does, contact the maintainer since this
-- indicates a bug\/insecurity in this library.
fromFin :: ReflectNum n => Fin n -> Int
fromFin x@(Fin i) = i `checking` x
{-# INLINE fromFin #-}


-- | Safely embed a number into @Fin n@. Use of this function will
-- generally require an explicit type signature in order to know
-- which @n@ to use.
toFin :: forall n. ReflectNum n => Int -> Maybe (Fin n)
toFin i
    | 0 <= i && i <= maxBoundOf x = Just x
    | otherwise                   = Nothing
    where
    x = Fin i :: Fin n
{-# INLINE toFin #-}

-- TODO: RULES for toFin.fromFin and fromFin.toFin


-- | Safely embed integers into @Fin n@, where @n@ is the first
-- argument. We use rank-2 polymorphism to render the type-level
-- @n@ existentially quantified, thereby hiding the dependent type
-- from the compiler. That is, given the call @toFinCPS n k i@, if
-- @i@ is a valid element of @Fin n@ then we will pass it to the
-- continuation @k@ and wrap the result in @Just@; otherwise we
-- return @Nothing@.
toFinCPS :: Int -> (forall n. ReflectNum n => Fin n -> r) -> Int -> Maybe r
toFinCPS n k i
    | 0 <= i && i < n = Just (reifyInt n $ \(_::n) -> k (Fin i :: Fin n))
    | otherwise       = Nothing
{-# INLINE toFinCPS #-}


----------------------------------------------------------------
instance ReflectNum n => QC.Arbitrary (Fin n) where
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
        


instance ReflectNum n => QC.CoArbitrary (Fin n) where
    coarbitrary (Fin n) = QC.variant n


instance ReflectNum n => SC.Serial (Fin n) where
    series d
        | d < 0     = [] -- paranoia.
        | otherwise =
            case toFin d of
            Nothing -> enumFromTo minBound maxBound
            Just n  -> enumFromTo minBound n
    
    coseries rs d =
        [ \(Fin i) ->
            if i > 0
            then f (check (Fin (i-1) :: Fin n)) -- more paranoia.
            else z
        | z <- SC.alts0 rs d
        , f <- SC.alts1 rs d
        ]

instance ReflectNum n => LSC.Serial (Fin n) where
    series = LSC.drawnFrom . SC.series

----------------------------------------------------------------
{-
-- This type-restricted version is a la Agda.
-- TODO: needs type-level function Succ.
-- | Embed finite domains into larger ones.
weaken :: Fin n -> Fin (Succ n)
weaken (Fin x) = Fin x
-}

-- | Embed finite domains into larger ones, keeping the same position
-- relative to 'minBound'. That is:
--
-- > fromFin x == fromFin (weakenLE x)
--
-- Use of this function will generally require an explicit type
-- signature in order to know which @n@ to use.
weakenLE :: (ReflectNum n, ReflectNum m, LE m n) => Fin m -> Fin n
weakenLE (Fin i) = Fin i
{-# INLINE weakenLE #-}


-- TODO: widen :: Fin n -> Fin (Succ n)


-- | Embed finite domains into larger ones, keeping the same position
-- relative to 'maxBound'. That is:
--
-- > maxBoundOf x - fromFin x == maxBoundOf y - fromFin y
-- >     where y = weakenLE x
--
-- Use of this function will generally require an explicit type
-- signature in order to know which @n@ to use.
widenLE :: (ReflectNum m, ReflectNum n, LE m n) => Fin m -> Fin n
widenLE x@(Fin i) = y
    where
    y = Fin (maxBoundOf y - maxBoundOf x + i)
{-# INLINE widenLE #-}


{- -- TODO: define Plus so that we can implement the monoidal structure of the (skeleton of the) augmented simplex category <http://ncatlab.org/nlab/show/simplex+category>:

-- | An optimization of 'widenLE'.
widenPlus :: (ReflectNum m, ReflectNum n) => Fin n -> Fin (Plus m n)
widenPlus y = Fin (maxBoundOf (__::Fin m) + fromFin y)


plus :: (ReflectNum m, ReflectNum n)
     => Either (Fin m) (Fin n) -> Fin (Plus m n)
plus = either weakenLE widenPlus


fplus :: (ReflectNum m, ReflectNum n, ReflectNum m', ReflectNum n')
       => (Fin m -> Fin m')
       -> (Fin n -> Fin n')
       -> Fin (Plus m n) -> Fin (Plus m' n')
fplus f g (Fin i)
    | i <= x    = weakenLE  (f (Fin i))
    | otherwise = widenPlus (g $! Fin (i-x))
    where
    x = maxBoundOf (__ :: Fin m)


unplus :: (ReflectNum m, ReflectNum n)
       => Fin (Plus m n) -> Either (Fin m) (Fin n)
unplus (Fin i)
    | i <= x    = Left (Fin i)
    | otherwise = Right $! Fin (i-x)
    where
    x = maxBoundOf (__ :: Fin m)
-}

{-
Agda also provides the following views:

-- A view telling you if a given element is the maximal one.
data MaxView {n : Nat} : Fin (suc n) -> Set where
  theMax : MaxView (fromNat n)
  notMax : (i : Fin n) -> MaxView (weaken i)

maxView : {n : Nat}(i : Fin (suc n)) -> MaxView i
maxView {zero} zero = theMax
maxView {zero} (suc ())
maxView {suc n} zero = notMax zero
maxView {suc n} (suc i) with maxView i
maxView {suc n} (suc .(fromNat n)) | theMax   = theMax
maxView {suc n} (suc .(weaken i))  | notMax i = notMax (suc i)


-- ueh? this is just another way to test for n==0; why bother with this? The only possible use I could see is to say, hey I have an actual value of Fin n, therefore n can't be zero... but then if you had a purported value of Fin n and that wasn't the case, then you'd have a contradiction to work with, ne?
-- The non zero view, which is used for defining compare...
data NonEmptyView : {n : Nat} -> Fin n -> Set where
  ne : {n : Nat}{i : Fin (suc n)} -> NonEmptyView i

nonEmpty : {n : Nat}(i : Fin n) -> NonEmptyView i
nonEmpty zero    = ne
nonEmpty (suc _) = ne


-- | The \"face maps\" for @Fin@ viewed as the standard simplices.
-- For each @i@, it is the unique injective monotonic map that skips
-- @i@. Traditionally spelled with delta or epsilon. AKA, the
-- thinning view.
--
-- > thin i j == if j < i then weaken j else succ (weaken j)
-- > thin i j /= i
--
thin : {n : Nat} -> Fin (suc n) -> Fin n -> Fin (suc n)
thin zero    j       = suc j
thin (suc i) zero    = zero
thin (suc i) (suc j) = suc (thin i j)

-- TODO:
-- | The \"degeneracy maps\" for @Fin@ viewed as the standard
-- simplices. For each @i@, it is the unique surjective monotonic
-- map that covers @i@ twice. Traditionally spelled with sigma or
-- eta.
--
-- > thick i j == if j <= i then strengthen j else strengthen (pred j)
-- > thick i (i+1) == i
--
thick : {n : Nat} -> Fin n -> Fin (suc n) -> Fin n

-- <http://ncatlab.org/nlab/show/simplex+category>


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
