{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
{-# LANGUAGE EmptyDataDecls
           , DeriveDataTypeable
           , Rank2Types
           , ScopedTypeVariables
           , MultiParamTypeClasses
           , FlexibleContexts
           , FlexibleInstances
           , UndecidableInstances
           , FunctionalDependencies
           #-}
----------------------------------------------------------------
--                                                    2013.01.04
-- |
-- Module      :  Data.Number.Fin.TyInteger
-- Copyright   :  2012--2013 wren ng thornton,
--                2004--2007 Oleg Kiselyov and Chung-chieh Shan
-- License     :  BSD3
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Type-level unbounded integers. This is based on [1], and is
-- intended to work with [2] (though we use the @reflection@ package
-- for the actual reification part).
--
-- Note that the terms \"reify\" and \"reflect\" may seem to be
-- used in a way which is the reverse of what one might intuit.
-- Here, the representation of a number in type-level decimal is
-- considered \"real\". Thus to turn a value into a type-level term
-- is to \"reify\" it; to go the other way is to \"reflect\".
--
-- Recent versions of GHC have type-level natural number literals.
-- Ideally, this module would be completely obviated by that work.
-- Unfortunately, the type-level literals aren't quite ready for
-- prime time yet, because they do not have a solver. Thus, we're
-- implementing here stuff that should be handled natively by GHC
-- in the future. A lot of this also duplicates the functionality
-- in @HList:Data.HList.FakePrelude@[3], which is (or should be)
-- obviated by the new data kinds extension.
--
-- [1] Oleg Kiselyov and Chung-chieh Shan. (2007) /Lightweight/
--     /static resources: Sexy types for embedded and systems/
--     /programming/. Proc. Trends in Functional Programming.
--     New York, 2--4 April 2007.
--     <http://okmij.org/ftp/Haskell/types.html#binary-arithm>
--
-- [2] Oleg Kiselyov and Chung-chieh Shan. (2004) /Implicit/
--     /configurations: or, type classes reflect the values of/
--     /types/. Proc. ACM SIGPLAN 2004 workshop on Haskell.
--     Snowbird, Utah, USA, 22 September 2004. pp.33--44.
--     <http://okmij.org/ftp/Haskell/types.html#Prepose>
--
-- [3] <http://hackage.haskell.org/package/HList>
----------------------------------------------------------------
module Data.Number.Fin.TyInteger
    (
    -- * The new code
      OfType()
    , getValueOfType
    -- * The original code
    , reifyIntegral
    , reifyInt
    , ReflectNum(..)
    -- * Notation for constructing type-level integers
    -- ** The @TyInteger@ kind
    , Positive
    , Negative
    -- ** The @TyUnsigned@ kind
    -- |  Note, digits are given in big-endian order; thus the type
    -- @(D3 (D2 D_))@ is the reification of @32@.
    , D_
    , D0
    , D1
    , D2
    , D3
    , D4
    , D5
    , D6
    , D7
    , D8
    , D9
    -- ** Shorthands for some small numbers
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
    -- ** Shorthands for some large numbers
    , MinBoundInt8,  MaxBoundInt8
    , MinBoundInt16, MaxBoundInt16
    , MinBoundInt32, MaxBoundInt32
    , MinBoundInt64, MaxBoundInt64
    -- MinBoundInt, MaxBoundInt
    , MaxBoundWord8
    , MaxBoundWord16
    , MaxBoundWord32
    , MaxBoundWord64
    -- MaxBoundWord
    
    -- * Some classes for manipulating type-level integers
    , LE()
    -- Pred()
    -- Succ()
    -- Plus()
    ) where

import Data.Int
import Data.Word
import Data.Monoid     (Monoid(..))
import Data.Typeable   (Typeable)
import Data.Proxy      (Proxy(Proxy))
import Data.Reflection (Reifies(..))
----------------------------------------------------------------

here :: String
here = "Data.Number.Fin.TyInteger"

__ :: forall a. a
__ = error $ here ++": attempted to evaluate type token"
-- TODO: use extensible-exceptions instead of 'error'

-- | A sentinel type, denoting the decimal point.
data D_ deriving Typeable
-- | The digit 0.
data D0 n deriving Typeable
-- | The digit 1.
data D1 n deriving Typeable
-- | The digit 2.
data D2 n deriving Typeable
-- | The digit 3.
data D3 n deriving Typeable
-- | The digit 4.
data D4 n deriving Typeable
-- | The digit 5.
data D5 n deriving Typeable
-- | The digit 6.
data D6 n deriving Typeable
-- | The digit 7.
data D7 n deriving Typeable
-- | The digit 8.
data D8 n deriving Typeable
-- | The digit 9.
data D9 n deriving Typeable
-- | The positive sign.
data Positive n deriving Typeable
-- | The negative sign.
data Negative n deriving Typeable

type Zero  = Positive D_
type One   = Positive (D1 D_)
type Two   = Positive (D2 D_)
type Three = Positive (D3 D_)
type Four  = Positive (D4 D_)
type Five  = Positive (D5 D_)
type Six   = Positive (D6 D_)
type Seven = Positive (D7 D_)
type Eight = Positive (D8 D_)
type Nine  = Positive (D9 D_)

type MinBoundInt8  = Negative (D1(D2(D8 D_)))
type MaxBoundInt8  = Positive (D1(D2(D7 D_)))
type MinBoundInt16 = Negative (D3(D2 (D7(D6(D8 D_)))))
type MaxBoundInt16 = Positive (D3(D2 (D7(D6(D7 D_)))))
type MinBoundInt32 = Negative (D2 (D1(D4(D7 (D4(D8(D3 (D6(D4(D8 D_))))))))))
type MaxBoundInt32 = Positive (D2 (D1(D4(D7 (D4(D8(D3 (D6(D4(D7 D_))))))))))
type MinBoundInt64 =
    Negative (D9 (D2(D2(D3 (D3(D7(D2 (D0(D3(D6 (D8(D5(D4 (D7(D7(D5 (D8(D0(D8
    D_)))))))))))))))))))
type MaxBoundInt64 =
    Positive (D9 (D2(D2(D3 (D3(D7(D2 (D0(D3(D6 (D8(D5(D4 (D7(D7(D5 (D8(D0(D7
    D_)))))))))))))))))))

-- TODO: MinBoundInt
-- TODO: MaxBoundInt

type MaxBoundWord8  = Positive (D2(D5(D5 D_)))
type MaxBoundWord16 = Positive (D6(D5 (D5(D3(D5 D_)))))
type MaxBoundWord32 = Positive (D4 (D2(D9(D4 (D9(D6(D7 (D2(D9(D5 D_))))))))))
type MaxBoundWord64 =
    Positive (D1(D8 (D4(D4(D6 (D7(D4(D4 (D0(D7(D3 (D7(D0(D9 (D5(D5(D1 (D6(D1(D5
    D_))))))))))))))))))))

-- TODO: MaxBoundWord

----------------------------------------------------------------

class ReflectUnsigned n where
    reflectUnsigned :: n -> Int -> Int

instance ReflectUnsigned D_ where
    reflectUnsigned _ n = n
instance ReflectUnsigned s => ReflectUnsigned (D0 s) where
    reflectUnsigned _ n = reflectUnsigned (__ :: s) (0 + 10*n)
instance ReflectUnsigned s => ReflectUnsigned (D1 s) where
    reflectUnsigned _ n = reflectUnsigned (__ :: s) (1 + 10*n)
instance ReflectUnsigned s => ReflectUnsigned (D2 s) where
    reflectUnsigned _ n = reflectUnsigned (__ :: s) (2 + 10*n)
instance ReflectUnsigned s => ReflectUnsigned (D3 s) where
    reflectUnsigned _ n = reflectUnsigned (__ :: s) (3 + 10*n)
instance ReflectUnsigned s => ReflectUnsigned (D4 s) where
    reflectUnsigned _ n = reflectUnsigned (__ :: s) (4 + 10*n)
instance ReflectUnsigned s => ReflectUnsigned (D5 s) where
    reflectUnsigned _ n = reflectUnsigned (__ :: s) (5 + 10*n)
instance ReflectUnsigned s => ReflectUnsigned (D6 s) where
    reflectUnsigned _ n = reflectUnsigned (__ :: s) (6 + 10*n)
instance ReflectUnsigned s => ReflectUnsigned (D7 s) where
    reflectUnsigned _ n = reflectUnsigned (__ :: s) (7 + 10*n)
instance ReflectUnsigned s => ReflectUnsigned (D8 s) where
    reflectUnsigned _ n = reflectUnsigned (__ :: s) (8 + 10*n)
instance ReflectUnsigned s => ReflectUnsigned (D9 s) where
    reflectUnsigned _ n = reflectUnsigned (__ :: s) (9 + 10*n)


class ReflectNum s where
    -- | Reflect a type-level number to a value-level 'Int'. N.B.,
    -- it is unspecified what the result should be when the type-level
    -- number is larger that can fit into 'Int'.
    reflectNum :: s -> Int

instance ReflectUnsigned s => ReflectNum (Positive s) where
    reflectNum _ = reflectUnsigned (__ :: s) 0
instance ReflectUnsigned s => ReflectNum (Negative s) where
    reflectNum _ = negate (reflectUnsigned (__ :: s) 0)


revDigits :: Integral a => a -> [a]
revDigits 0 = []
revDigits n = let (d,m) = divMod n 10 in m : revDigits d


digits :: Integral a => a -> [a]
digits = reverse . revDigits


-- | N.B., the argument will be coerced to 'Int' via 'fromIntegral'
-- before reification.
reifyIntegral :: Integral a => a -> (forall s. ReflectNum s => s -> w) -> w
reifyIntegral i k = reifyInt (fromIntegral i) k


reifyInt :: Int -> (forall s. ReflectNum s => s -> w) -> w
reifyInt i k =
    if i >= 0
    then reifyDigits (digits i)          (\ (_ :: s) -> k (__ :: Positive s))
    else reifyDigits (digits $ negate i) (\ (_ :: s) -> k (__ :: Negative s))


reifyDigits :: [Int] -> (forall s. ReflectUnsigned s => s -> w) -> w
reifyDigits []     k = k (__ :: D_)
reifyDigits (i:is) k =
    case i of
    0 -> reifyDigits is (\ (_::s) -> k (__ :: D0 s))
    1 -> reifyDigits is (\ (_::s) -> k (__ :: D1 s))
    2 -> reifyDigits is (\ (_::s) -> k (__ :: D2 s))
    3 -> reifyDigits is (\ (_::s) -> k (__ :: D3 s))
    4 -> reifyDigits is (\ (_::s) -> k (__ :: D4 s))
    5 -> reifyDigits is (\ (_::s) -> k (__ :: D5 s))
    6 -> reifyDigits is (\ (_::s) -> k (__ :: D6 s))
    7 -> reifyDigits is (\ (_::s) -> k (__ :: D7 s))
    8 -> reifyDigits is (\ (_::s) -> k (__ :: D8 s))
    9 -> reifyDigits is (\ (_::s) -> k (__ :: D9 s))
    _ -> error $ here++".reifyDigits: the impossible happened"

----------------------------------------------------------------
----------------------------------------------------------------

-- Ideally we'd like to just use @(r -> r)@ with a @Num r@ constraint on the instance, but that requires FlexibleInstances since the @r@ is duplicated. So then we could try @Endo r@, but that requires UndecidableInstances since it violates the coverage condition, apparently. Thus, we end up with this type. Alas, it will almost surely interfere with all the inlining necessary to monomorphize and linearize the actual code. So the question is, which is more expensive: interpreting an DRepr datatype at known fixed types, or this polymorphic interpretation-less approach?
newtype DRepr = DRepr (forall r. Num r => r -> r)

instance Monoid DRepr where
    mempty                    = DRepr id
    DRepr f `mappend` DRepr g = DRepr (f .! g)
        where
        (.!) = (.) . ($!)

getDRepr :: Num r => DRepr -> r
getDRepr (DRepr f) = f 0

(<>) :: Monoid m => m -> m -> m
(<>) = mappend

-- BUG: this could still be screwed up if overlapping instances are allowed...
instance Reifies D_ DRepr where
    reflect _ = mempty
instance Reifies s DRepr => Reifies (D0 s) DRepr where
    reflect _ = reflect (Proxy :: Proxy s) <> DRepr (\n -> 0 + 10*n)
instance Reifies s DRepr => Reifies (D1 s) DRepr where
    reflect _ = reflect (Proxy :: Proxy s) <> DRepr (\n -> 1 + 10*n)
instance Reifies s DRepr => Reifies (D2 s) DRepr where
    reflect _ = reflect (Proxy :: Proxy s) <> DRepr (\n -> 2 + 10*n)
instance Reifies s DRepr => Reifies (D3 s) DRepr where
    reflect _ = reflect (Proxy :: Proxy s) <> DRepr (\n -> 3 + 10*n)
instance Reifies s DRepr => Reifies (D4 s) DRepr where
    reflect _ = reflect (Proxy :: Proxy s) <> DRepr (\n -> 4 + 10*n)
instance Reifies s DRepr => Reifies (D5 s) DRepr where
    reflect _ = reflect (Proxy :: Proxy s) <> DRepr (\n -> 5 + 10*n)
instance Reifies s DRepr => Reifies (D6 s) DRepr where
    reflect _ = reflect (Proxy :: Proxy s) <> DRepr (\n -> 6 + 10*n)
instance Reifies s DRepr => Reifies (D7 s) DRepr where
    reflect _ = reflect (Proxy :: Proxy s) <> DRepr (\n -> 7 + 10*n)
instance Reifies s DRepr => Reifies (D8 s) DRepr where
    reflect _ = reflect (Proxy :: Proxy s) <> DRepr (\n -> 8 + 10*n)
instance Reifies s DRepr => Reifies (D9 s) DRepr where
    reflect _ = reflect (Proxy :: Proxy s) <> DRepr (\n -> 9 + 10*n)


-- | Values of type @x `OfType` a@ are proofs that (the reflection
-- of) @x@ has type @a@. Of course there's an easy proof: the
-- reflection of @x@ as an actual value of type @a@; hence, this
-- is a singleton type whose only value is the reflection of @x@
-- at type @a@.
--
-- The name is chosen to support infix use. And, indeed, you can use it infix--- provided @TypeOperators@ is enabled.
newtype OfType x a = OfType a
    deriving (Read, Show, Eq, Ord)
    -- N.B., do not export the constructor; else this is equivalent to @Tagged x a@, which allows people to change the tag!

-- | Given a proof that @x@ is of type @a@, return @x@.
getValueOfType :: OfType x a -> a
getValueOfType (OfType a) = a
{-# INLINE getValueOfType #-}

{- TODO: prove correct so that we can use these optimized instances
instance Eq (OfType x a) where
    _ == _ = True
    _ /= _ = False

instance Ord (OfType x a) where
    compare _ _ = EQ
    _ <  _ = False
    _ >= _ = True
    _ >  _ = False
    _ <= _ = True
    max x _ = x
    min x _ = x
-}

-- These instances are "undecidable" because of the LE constraints.
instance
    (LE (Positive n) MaxBoundInt8, Reifies n DRepr)
    => Reifies (OfType (Positive n) Int8) (OfType (Positive n) Int8)
    where reflect _ = OfType (getDRepr (reflect (Proxy :: Proxy n)))
instance
    (LE MinBoundInt8 (Negative n), Reifies n DRepr)
    => Reifies (OfType (Negative n) Int8) (OfType (Negative n) Int8)
    where reflect _ = OfType (negate (getDRepr (reflect (Proxy :: Proxy n))))

instance
    (LE (Positive n) MaxBoundInt16, Reifies n DRepr)
    => Reifies (OfType (Positive n) Int16) (OfType (Positive n) Int16)
    where reflect _ = OfType (getDRepr (reflect (Proxy :: Proxy n)))
instance
    (LE MinBoundInt16 (Negative n), Reifies n DRepr)
    => Reifies (OfType (Negative n) Int16) (OfType (Negative n) Int16)
    where reflect _ = OfType (negate (getDRepr (reflect (Proxy :: Proxy n))))

instance
    (LE (Positive n) MaxBoundInt32, Reifies n DRepr)
    => Reifies (OfType (Positive n) Int32) (OfType (Positive n) Int32)
    where reflect _ = OfType (getDRepr (reflect (Proxy :: Proxy n)))
instance
    (LE MinBoundInt32 (Negative n), Reifies n DRepr)
    => Reifies (OfType (Negative n) Int32) (OfType (Negative n) Int32)
    where reflect _ = OfType (negate (getDRepr (reflect (Proxy :: Proxy n))))

instance
    (LE (Positive n) MaxBoundInt64, Reifies n DRepr)
    => Reifies (OfType (Positive n) Int64) (OfType (Positive n) Int64)
    where reflect _ = OfType (getDRepr (reflect (Proxy :: Proxy n)))
instance
    (LE MinBoundInt64 (Negative n), Reifies n DRepr)
    => Reifies (OfType (Negative n) Int64) (OfType (Negative n) Int64)
    where reflect _ = OfType (negate (getDRepr (reflect (Proxy :: Proxy n))))

{- TODO
instance
    (LE (Positive n) MaxBoundInt, Reifies n DRepr)
    => Reifies (OfType (Positive n) Int) (OfType (Positive n) Int)
    where reflect _ = OfType (getDRepr (reflect (Proxy :: Proxy n)))
instance
    (LE MinBoundInt (Negative n), Reifies n DRepr)
    => Reifies (OfType (Negative n) Int) (OfType (Negative n) Int)
    where reflect _ = OfType (negate (getDRepr (reflect (Proxy :: Proxy n))))
-}

instance
    (LE (Positive n) MaxBoundWord8, Reifies n DRepr)
    => Reifies (OfType (Positive n) Word8) (OfType (Positive n) Word8)
    where reflect _ = OfType (getDRepr (reflect (Proxy :: Proxy n)))
instance
    (LE (Positive n) MaxBoundWord16, Reifies n DRepr)
    => Reifies (OfType (Positive n) Word16) (OfType (Positive n) Word16)
    where reflect _ = OfType (getDRepr (reflect (Proxy :: Proxy n)))
instance
    (LE (Positive n) MaxBoundWord32, Reifies n DRepr)
    => Reifies (OfType (Positive n) Word32) (OfType (Positive n) Word32)
    where reflect _ = OfType (getDRepr (reflect (Proxy :: Proxy n)))
instance
    (LE (Positive n) MaxBoundWord64, Reifies n DRepr)
    => Reifies (OfType (Positive n) Word64) (OfType (Positive n) Word64)
    where reflect _ = OfType (getDRepr (reflect (Proxy :: Proxy n)))
{-
instance
    (LE (Positive n) MaxBoundWord, Reifies n DRepr)
    => Reifies (OfType (Positive n) Word) (OfType (Positive n) Word)
    where reflect _ = OfType (getDRepr (reflect (Proxy :: Proxy n)))
-}


----------------------------------------------------------------
----------------------------------------------------------------

-- | Is @n@ a valid type of kind @TyUnsigned@?
class TyUnsigned_ n
instance                   TyUnsigned_ D_
instance                   TyUnsigned_ (D0 D_)
instance TyUnsigned_' n => TyUnsigned_ (D1 n)
instance TyUnsigned_' n => TyUnsigned_ (D2 n)
instance TyUnsigned_' n => TyUnsigned_ (D3 n)
instance TyUnsigned_' n => TyUnsigned_ (D4 n)
instance TyUnsigned_' n => TyUnsigned_ (D5 n)
instance TyUnsigned_' n => TyUnsigned_ (D6 n)
instance TyUnsigned_' n => TyUnsigned_ (D7 n)
instance TyUnsigned_' n => TyUnsigned_ (D8 n)
instance TyUnsigned_' n => TyUnsigned_ (D9 n)

-- | Is @n@ type which, when the extraneous leading zeros are dropped, is a valid type of kind @TyUnsigned@?
class TyUnsigned_' n
instance                   TyUnsigned_' D_
instance TyUnsigned_' n => TyUnsigned_' (D0 n)
instance TyUnsigned_' n => TyUnsigned_' (D1 n)
instance TyUnsigned_' n => TyUnsigned_' (D2 n)
instance TyUnsigned_' n => TyUnsigned_' (D3 n)
instance TyUnsigned_' n => TyUnsigned_' (D4 n)
instance TyUnsigned_' n => TyUnsigned_' (D5 n)
instance TyUnsigned_' n => TyUnsigned_' (D6 n)
instance TyUnsigned_' n => TyUnsigned_' (D7 n)
instance TyUnsigned_' n => TyUnsigned_' (D8 n)
instance TyUnsigned_' n => TyUnsigned_' (D9 n)

-- | Is @length m <= length n@?
class (TyUnsigned_' m, TyUnsigned_' n) => LELength_ m n
instance                   LELength_ D_     D_
instance TyUnsigned_' n => LELength_ D_     (D0 n)
instance TyUnsigned_' n => LELength_ D_     (D1 n)
instance TyUnsigned_' n => LELength_ D_     (D2 n)
instance TyUnsigned_' n => LELength_ D_     (D3 n)
instance TyUnsigned_' n => LELength_ D_     (D4 n)
instance TyUnsigned_' n => LELength_ D_     (D5 n)
instance TyUnsigned_' n => LELength_ D_     (D6 n)
instance TyUnsigned_' n => LELength_ D_     (D7 n)
instance TyUnsigned_' n => LELength_ D_     (D8 n)
instance TyUnsigned_' n => LELength_ D_     (D9 n)
instance LELength_ m n  => LELength_ (D0 m) (D0 n)
instance LELength_ m n  => LELength_ (D0 m) (D1 n)
instance LELength_ m n  => LELength_ (D0 m) (D2 n)
instance LELength_ m n  => LELength_ (D0 m) (D3 n)
instance LELength_ m n  => LELength_ (D0 m) (D4 n)
instance LELength_ m n  => LELength_ (D0 m) (D5 n)
instance LELength_ m n  => LELength_ (D0 m) (D6 n)
instance LELength_ m n  => LELength_ (D0 m) (D7 n)
instance LELength_ m n  => LELength_ (D0 m) (D8 n)
instance LELength_ m n  => LELength_ (D0 m) (D9 n)
instance LELength_ m n  => LELength_ (D1 m) (D0 n)
instance LELength_ m n  => LELength_ (D1 m) (D1 n)
instance LELength_ m n  => LELength_ (D1 m) (D2 n)
instance LELength_ m n  => LELength_ (D1 m) (D3 n)
instance LELength_ m n  => LELength_ (D1 m) (D4 n)
instance LELength_ m n  => LELength_ (D1 m) (D5 n)
instance LELength_ m n  => LELength_ (D1 m) (D6 n)
instance LELength_ m n  => LELength_ (D1 m) (D7 n)
instance LELength_ m n  => LELength_ (D1 m) (D8 n)
instance LELength_ m n  => LELength_ (D1 m) (D9 n)
instance LELength_ m n  => LELength_ (D2 m) (D0 n)
instance LELength_ m n  => LELength_ (D2 m) (D1 n)
instance LELength_ m n  => LELength_ (D2 m) (D2 n)
instance LELength_ m n  => LELength_ (D2 m) (D3 n)
instance LELength_ m n  => LELength_ (D2 m) (D4 n)
instance LELength_ m n  => LELength_ (D2 m) (D5 n)
instance LELength_ m n  => LELength_ (D2 m) (D6 n)
instance LELength_ m n  => LELength_ (D2 m) (D7 n)
instance LELength_ m n  => LELength_ (D2 m) (D8 n)
instance LELength_ m n  => LELength_ (D2 m) (D9 n)
instance LELength_ m n  => LELength_ (D3 m) (D0 n)
instance LELength_ m n  => LELength_ (D3 m) (D1 n)
instance LELength_ m n  => LELength_ (D3 m) (D2 n)
instance LELength_ m n  => LELength_ (D3 m) (D3 n)
instance LELength_ m n  => LELength_ (D3 m) (D4 n)
instance LELength_ m n  => LELength_ (D3 m) (D5 n)
instance LELength_ m n  => LELength_ (D3 m) (D6 n)
instance LELength_ m n  => LELength_ (D3 m) (D7 n)
instance LELength_ m n  => LELength_ (D3 m) (D8 n)
instance LELength_ m n  => LELength_ (D3 m) (D9 n)
instance LELength_ m n  => LELength_ (D4 m) (D0 n)
instance LELength_ m n  => LELength_ (D4 m) (D1 n)
instance LELength_ m n  => LELength_ (D4 m) (D2 n)
instance LELength_ m n  => LELength_ (D4 m) (D3 n)
instance LELength_ m n  => LELength_ (D4 m) (D4 n)
instance LELength_ m n  => LELength_ (D4 m) (D5 n)
instance LELength_ m n  => LELength_ (D4 m) (D6 n)
instance LELength_ m n  => LELength_ (D4 m) (D7 n)
instance LELength_ m n  => LELength_ (D4 m) (D8 n)
instance LELength_ m n  => LELength_ (D4 m) (D9 n)
instance LELength_ m n  => LELength_ (D5 m) (D0 n)
instance LELength_ m n  => LELength_ (D5 m) (D1 n)
instance LELength_ m n  => LELength_ (D5 m) (D2 n)
instance LELength_ m n  => LELength_ (D5 m) (D3 n)
instance LELength_ m n  => LELength_ (D5 m) (D4 n)
instance LELength_ m n  => LELength_ (D5 m) (D5 n)
instance LELength_ m n  => LELength_ (D5 m) (D6 n)
instance LELength_ m n  => LELength_ (D5 m) (D7 n)
instance LELength_ m n  => LELength_ (D5 m) (D8 n)
instance LELength_ m n  => LELength_ (D5 m) (D9 n)
instance LELength_ m n  => LELength_ (D6 m) (D0 n)
instance LELength_ m n  => LELength_ (D6 m) (D1 n)
instance LELength_ m n  => LELength_ (D6 m) (D2 n)
instance LELength_ m n  => LELength_ (D6 m) (D3 n)
instance LELength_ m n  => LELength_ (D6 m) (D4 n)
instance LELength_ m n  => LELength_ (D6 m) (D5 n)
instance LELength_ m n  => LELength_ (D6 m) (D6 n)
instance LELength_ m n  => LELength_ (D6 m) (D7 n)
instance LELength_ m n  => LELength_ (D6 m) (D8 n)
instance LELength_ m n  => LELength_ (D6 m) (D9 n)
instance LELength_ m n  => LELength_ (D7 m) (D0 n)
instance LELength_ m n  => LELength_ (D7 m) (D1 n)
instance LELength_ m n  => LELength_ (D7 m) (D2 n)
instance LELength_ m n  => LELength_ (D7 m) (D3 n)
instance LELength_ m n  => LELength_ (D7 m) (D4 n)
instance LELength_ m n  => LELength_ (D7 m) (D5 n)
instance LELength_ m n  => LELength_ (D7 m) (D6 n)
instance LELength_ m n  => LELength_ (D7 m) (D7 n)
instance LELength_ m n  => LELength_ (D7 m) (D8 n)
instance LELength_ m n  => LELength_ (D7 m) (D9 n)
instance LELength_ m n  => LELength_ (D8 m) (D0 n)
instance LELength_ m n  => LELength_ (D8 m) (D1 n)
instance LELength_ m n  => LELength_ (D8 m) (D2 n)
instance LELength_ m n  => LELength_ (D8 m) (D3 n)
instance LELength_ m n  => LELength_ (D8 m) (D4 n)
instance LELength_ m n  => LELength_ (D8 m) (D5 n)
instance LELength_ m n  => LELength_ (D8 m) (D6 n)
instance LELength_ m n  => LELength_ (D8 m) (D7 n)
instance LELength_ m n  => LELength_ (D8 m) (D8 n)
instance LELength_ m n  => LELength_ (D8 m) (D9 n)
instance LELength_ m n  => LELength_ (D9 m) (D0 n)
instance LELength_ m n  => LELength_ (D9 m) (D1 n)
instance LELength_ m n  => LELength_ (D9 m) (D2 n)
instance LELength_ m n  => LELength_ (D9 m) (D3 n)
instance LELength_ m n  => LELength_ (D9 m) (D4 n)
instance LELength_ m n  => LELength_ (D9 m) (D5 n)
instance LELength_ m n  => LELength_ (D9 m) (D6 n)
instance LELength_ m n  => LELength_ (D9 m) (D7 n)
instance LELength_ m n  => LELength_ (D9 m) (D8 n)
instance LELength_ m n  => LELength_ (D9 m) (D9 n)


-- | A type class for representing the constraint that @m <= n@.
class LE m n where
-- This instance is "undecidable" because GHC can't see that LE_ dominates LE
instance LE_ m n => LE m n

class LE_ m n where
instance LE_ n m => LE_ (Negative m) (Negative n)
instance LE_ m n => LE_ (Positive m) (Positive n)
instance (TyUnsigned_ m, TyUnsigned_ n) => LE_ (Negative m) (Positive n)

instance                  LE_ D_     D_
instance TyUnsigned_ n => LE_ D_     (D0 n)
instance TyUnsigned_ n => LE_ D_     (D1 n)
instance TyUnsigned_ n => LE_ D_     (D2 n)
instance TyUnsigned_ n => LE_ D_     (D3 n)
instance TyUnsigned_ n => LE_ D_     (D4 n)
instance TyUnsigned_ n => LE_ D_     (D5 n)
instance TyUnsigned_ n => LE_ D_     (D6 n)
instance TyUnsigned_ n => LE_ D_     (D7 n)
instance TyUnsigned_ n => LE_ D_     (D8 n)
instance TyUnsigned_ n => LE_ D_     (D9 n)
instance LE_ m n       => LE_ (D0 m) (D0 n) -- BUG: or LE_ (D0 m) n
instance LELength_ m n => LE_ (D0 m) (D1 n)
instance LELength_ m n => LE_ (D0 m) (D2 n)
instance LELength_ m n => LE_ (D0 m) (D3 n)
instance LELength_ m n => LE_ (D0 m) (D4 n)
instance LELength_ m n => LE_ (D0 m) (D5 n)
instance LELength_ m n => LE_ (D0 m) (D6 n)
instance LELength_ m n => LE_ (D0 m) (D7 n)
instance LELength_ m n => LE_ (D0 m) (D8 n)
instance LELength_ m n => LE_ (D0 m) (D9 n)
instance LE_ (D1 m) n  => LE_ (D1 m) (D0 n)
instance LE_ m n       => LE_ (D1 m) (D1 n) -- BUG: or LE_ (D1 m) n
instance LELength_ m n => LE_ (D1 m) (D2 n)
instance LELength_ m n => LE_ (D1 m) (D3 n)
instance LELength_ m n => LE_ (D1 m) (D4 n)
instance LELength_ m n => LE_ (D1 m) (D5 n)
instance LELength_ m n => LE_ (D1 m) (D6 n)
instance LELength_ m n => LE_ (D1 m) (D7 n)
instance LELength_ m n => LE_ (D1 m) (D8 n)
instance LELength_ m n => LE_ (D1 m) (D9 n)
instance LE_ (D2 m) n  => LE_ (D2 m) (D0 n)
instance LE_ (D2 m) n  => LE_ (D2 m) (D1 n)
instance LE_ m n       => LE_ (D2 m) (D2 n) -- BUG: or LE_ (D2 m) n
instance LELength_ m n => LE_ (D2 m) (D3 n)
instance LELength_ m n => LE_ (D2 m) (D4 n)
instance LELength_ m n => LE_ (D2 m) (D5 n)
instance LELength_ m n => LE_ (D2 m) (D6 n)
instance LELength_ m n => LE_ (D2 m) (D7 n)
instance LELength_ m n => LE_ (D2 m) (D8 n)
instance LELength_ m n => LE_ (D2 m) (D9 n)
instance LE_ (D3 m) n  => LE_ (D3 m) (D0 n)
instance LE_ (D3 m) n  => LE_ (D3 m) (D1 n)
instance LE_ (D3 m) n  => LE_ (D3 m) (D2 n)
instance LE_ m n       => LE_ (D3 m) (D3 n) -- BUG: or LE_ (D3 m) n
instance LELength_ m n => LE_ (D3 m) (D4 n)
instance LELength_ m n => LE_ (D3 m) (D5 n)
instance LELength_ m n => LE_ (D3 m) (D6 n)
instance LELength_ m n => LE_ (D3 m) (D7 n)
instance LELength_ m n => LE_ (D3 m) (D8 n)
instance LELength_ m n => LE_ (D3 m) (D9 n)
instance LE_ (D4 m) n  => LE_ (D4 m) (D0 n)
instance LE_ (D4 m) n  => LE_ (D4 m) (D1 n)
instance LE_ (D4 m) n  => LE_ (D4 m) (D2 n)
instance LE_ (D4 m) n  => LE_ (D4 m) (D3 n)
instance LE_ m n       => LE_ (D4 m) (D4 n) -- BUG: or LE_ (D4 m) n
instance LELength_ m n => LE_ (D4 m) (D5 n)
instance LELength_ m n => LE_ (D4 m) (D6 n)
instance LELength_ m n => LE_ (D4 m) (D7 n)
instance LELength_ m n => LE_ (D4 m) (D8 n)
instance LELength_ m n => LE_ (D4 m) (D9 n)
instance LE_ (D5 m) n  => LE_ (D5 m) (D0 n)
instance LE_ (D5 m) n  => LE_ (D5 m) (D1 n)
instance LE_ (D5 m) n  => LE_ (D5 m) (D2 n)
instance LE_ (D5 m) n  => LE_ (D5 m) (D3 n)
instance LE_ (D5 m) n  => LE_ (D5 m) (D4 n)
instance LE_ m n       => LE_ (D5 m) (D5 n) -- BUG: or LE_ (D5 m) n
instance LELength_ m n => LE_ (D5 m) (D6 n)
instance LELength_ m n => LE_ (D5 m) (D7 n)
instance LELength_ m n => LE_ (D5 m) (D8 n)
instance LELength_ m n => LE_ (D5 m) (D9 n)
instance LE_ (D6 m) n  => LE_ (D6 m) (D0 n)
instance LE_ (D6 m) n  => LE_ (D6 m) (D1 n)
instance LE_ (D6 m) n  => LE_ (D6 m) (D2 n)
instance LE_ (D6 m) n  => LE_ (D6 m) (D3 n)
instance LE_ (D6 m) n  => LE_ (D6 m) (D4 n)
instance LE_ (D6 m) n  => LE_ (D6 m) (D5 n)
instance LE_ m n       => LE_ (D6 m) (D6 n) -- BUG: or LE_ (D6 m) n
instance LELength_ m n => LE_ (D6 m) (D7 n)
instance LELength_ m n => LE_ (D6 m) (D8 n)
instance LELength_ m n => LE_ (D6 m) (D9 n)
instance LE_ (D7 m) n  => LE_ (D7 m) (D0 n)
instance LE_ (D7 m) n  => LE_ (D7 m) (D1 n)
instance LE_ (D7 m) n  => LE_ (D7 m) (D2 n)
instance LE_ (D7 m) n  => LE_ (D7 m) (D3 n)
instance LE_ (D7 m) n  => LE_ (D7 m) (D4 n)
instance LE_ (D7 m) n  => LE_ (D7 m) (D5 n)
instance LE_ (D7 m) n  => LE_ (D7 m) (D6 n)
instance LE_ m n       => LE_ (D7 m) (D7 n) -- BUG: or LE_ (D7 m) n
instance LELength_ m n => LE_ (D7 m) (D8 n)
instance LELength_ m n => LE_ (D7 m) (D9 n)
instance LE_ (D8 m) n  => LE_ (D8 m) (D0 n)
instance LE_ (D8 m) n  => LE_ (D8 m) (D1 n)
instance LE_ (D8 m) n  => LE_ (D8 m) (D2 n)
instance LE_ (D8 m) n  => LE_ (D8 m) (D3 n)
instance LE_ (D8 m) n  => LE_ (D8 m) (D4 n)
instance LE_ (D8 m) n  => LE_ (D8 m) (D5 n)
instance LE_ (D8 m) n  => LE_ (D8 m) (D6 n)
instance LE_ (D8 m) n  => LE_ (D8 m) (D7 n)
instance LE_ m n       => LE_ (D8 m) (D8 n) -- BUG: or LE_ (D8 m) n
instance LELength_ m n => LE_ (D8 m) (D9 n)
instance LE_ (D9 m) n  => LE_ (D9 m) (D0 n)
instance LE_ (D9 m) n  => LE_ (D9 m) (D1 n)
instance LE_ (D9 m) n  => LE_ (D9 m) (D2 n)
instance LE_ (D9 m) n  => LE_ (D9 m) (D3 n)
instance LE_ (D9 m) n  => LE_ (D9 m) (D4 n)
instance LE_ (D9 m) n  => LE_ (D9 m) (D5 n)
instance LE_ (D9 m) n  => LE_ (D9 m) (D6 n)
instance LE_ (D9 m) n  => LE_ (D9 m) (D7 n)
instance LE_ (D9 m) n  => LE_ (D9 m) (D8 n)
instance LE_ m n       => LE_ (D9 m) (D9 n) -- BUG: or LE_ (D9 m) n


----------------------------------------------------------------
----------------------------------------------------------------
-- This is lexicographically big-endian, but structurally little-endian.
-- <http://okmij.org/ftp/Computation/resource-aware-prog/BinaryNumber.hs>
data X_ x y
data X0
data X1
data X2
data X3
data X4
data X5
data X6
data X7
data X8
data X9

-- | The whole numbers; aka, the natural numbers except for zero.
class XNatural_ x => XNaturalNE0_ x
instance                   XNaturalNE0_ X1
instance                   XNaturalNE0_ X2
instance                   XNaturalNE0_ X3
instance                   XNaturalNE0_ X4
instance                   XNaturalNE0_ X5
instance                   XNaturalNE0_ X6
instance                   XNaturalNE0_ X7
instance                   XNaturalNE0_ X8
instance                   XNaturalNE0_ X9
instance XNaturalNE0_ x => XNaturalNE0_ (X_ x X0)
instance XNaturalNE0_ x => XNaturalNE0_ (X_ x X1)
instance XNaturalNE0_ x => XNaturalNE0_ (X_ x X2)
instance XNaturalNE0_ x => XNaturalNE0_ (X_ x X3)
instance XNaturalNE0_ x => XNaturalNE0_ (X_ x X4)
instance XNaturalNE0_ x => XNaturalNE0_ (X_ x X5)
instance XNaturalNE0_ x => XNaturalNE0_ (X_ x X6)
instance XNaturalNE0_ x => XNaturalNE0_ (X_ x X7)
instance XNaturalNE0_ x => XNaturalNE0_ (X_ x X8)
instance XNaturalNE0_ x => XNaturalNE0_ (X_ x X9)

-- In Oleg's version, this class does the work of reflection...
-- | The natural numbers (including zero).
class XNatural_ x
instance                   XNatural_ X0
instance                   XNatural_ X1
instance                   XNatural_ X2
instance                   XNatural_ X3
instance                   XNatural_ X4
instance                   XNatural_ X5
instance                   XNatural_ X6
instance                   XNatural_ X7
instance                   XNatural_ X8
instance                   XNatural_ X9
instance XNaturalNE0_ x => XNatural_ (X_ x X0)
instance XNaturalNE0_ x => XNatural_ (X_ x X1)
instance XNaturalNE0_ x => XNatural_ (X_ x X2)
instance XNaturalNE0_ x => XNatural_ (X_ x X3)
instance XNaturalNE0_ x => XNatural_ (X_ x X4)
instance XNaturalNE0_ x => XNatural_ (X_ x X5)
instance XNaturalNE0_ x => XNatural_ (X_ x X6)
instance XNaturalNE0_ x => XNatural_ (X_ x X7)
instance XNaturalNE0_ x => XNatural_ (X_ x X8)
instance XNaturalNE0_ x => XNatural_ (X_ x X9)

-- | Successor; by structural induction on the first argument.
class (XNatural_ x, XNaturalNE0_ y) => Succ x y | x -> y, y -> x
instance                   Succ X0        X1
instance                   Succ X1        X2
instance                   Succ X2        X3
instance                   Succ X3        X4
instance                   Succ X4        X5
instance                   Succ X5        X6
instance                   Succ X6        X7
instance                   Succ X7        X8
instance                   Succ X8        X9
instance                   Succ X9        (X_ X1 X0)
instance XNaturalNE0_ x => Succ (X_ x X0) (X_ x X1)
instance XNaturalNE0_ x => Succ (X_ x X1) (X_ x X2)
instance XNaturalNE0_ x => Succ (X_ x X2) (X_ x X3)
instance XNaturalNE0_ x => Succ (X_ x X3) (X_ x X4)
instance XNaturalNE0_ x => Succ (X_ x X4) (X_ x X5)
instance XNaturalNE0_ x => Succ (X_ x X5) (X_ x X6)
instance XNaturalNE0_ x => Succ (X_ x X6) (X_ x X7)
instance XNaturalNE0_ x => Succ (X_ x X7) (X_ x X8)
instance XNaturalNE0_ x => Succ (X_ x X8) (X_ x X9)
-- This triggers the need for undecidable instances <sigh>
-- The expansion of (X_ y z) is to avoid fundep conflict with: X9 (X_ X1 X0)
instance (XNaturalNE0_ x, Succ x (X_ y z)) => Succ (X_ x X9) (X_ (X_ y z) X0)


-- TODO: there's gotta be a more efficient way than iterated Succ...
-- | Primitive addition; by structural induction on the first argument.
class (XNatural_ x, XNatural_ y, XNatural_ z)
    => Add_ x y z | x y -> z, z x -> y
instance (XNatural_ y)                       => Add_ X0 y y
instance (Succ y y1)                         => Add_ X1 y y1
instance (Succ y y1, Succ y1 y2)             => Add_ X2 y y2
instance (Succ y y1, Succ y1 y2, Succ y2 y3) => Add_ X3 y y3
instance
    ( Succ y  y1, Succ y1 y2, Succ y2 y3
    , Succ y3 y4
    ) => Add_ X4 y y4
instance
    ( Succ y  y1, Succ y1 y2, Succ y2 y3
    , Succ y3 y4, Succ y4 y5
    ) => Add_ X5 y y5
instance
    ( Succ y  y1, Succ y1 y2, Succ y2 y3
    , Succ y3 y4, Succ y4 y5, Succ y5 y6
    ) => Add_ X6 y y6
instance
    ( Succ y  y1, Succ y1 y2, Succ y2 y3
    , Succ y3 y4, Succ y4 y5, Succ y5 y6
    , Succ y6 y7
    ) => Add_ X7 y y7
instance
    ( Succ y  y1, Succ y1 y2, Succ y2 y3
    , Succ y3 y4, Succ y4 y5, Succ y5 y6
    , Succ y6 y7, Succ y7 y8
    ) => Add_ X8 y y8
instance
    ( Succ y  y1, Succ y1 y2, Succ y2 y3
    , Succ y3 y4, Succ y4 y5, Succ y5 y6
    , Succ y6 y7, Succ y7 y8, Succ y8 y9
    ) => Add_ X9 y y9
instance
    ( XNaturalNE0_ hx, XNaturalNE0_ (X_ hz tz)
    , Add_ hx hy hz
    , AppendX hy tz y
    ) => Add_ (X_ hx X0) y (X_ hz tz)
instance
    ( XNaturalNE0_ hx, XNatural_ z
    , Add_ hx hy hz
    , AppendX hy ty y
    , Add_ X1 (X_ hz ty) z
    ) => Add_ (X_ hx X1) y z
instance
    ( XNaturalNE0_ hx, XNatural_ z
    , Add_ hx hy hz
    , AppendX hy ty y
    , Add_ X2 (X_ hz ty) z
    ) => Add_ (X_ hx X2) y z
instance
    ( XNaturalNE0_ hx, XNatural_ z
    , Add_ hx hy hz
    , AppendX hy ty y
    , Add_ X3 (X_ hz ty) z
    ) => Add_ (X_ hx X3) y z
instance
    ( XNaturalNE0_ hx, XNatural_ z
    , Add_ hx hy hz
    , AppendX hy ty y
    , Add_ X4 (X_ hz ty) z
    ) => Add_ (X_ hx X4) y z
instance
    ( XNaturalNE0_ hx, XNatural_ z
    , Add_ hx hy hz
    , AppendX hy ty y
    , Add_ X5 (X_ hz ty) z
    ) => Add_ (X_ hx X5) y z
instance
    ( XNaturalNE0_ hx, XNatural_ z
    , Add_ hx hy hz
    , AppendX hy ty y
    , Add_ X6 (X_ hz ty) z
    ) => Add_ (X_ hx X6) y z
instance
    ( XNaturalNE0_ hx, XNatural_ z
    , Add_ hx hy hz
    , AppendX hy ty y
    , Add_ X7 (X_ hz ty) z
    ) => Add_ (X_ hx X7) y z
instance
    ( XNaturalNE0_ hx, XNatural_ z
    , Add_ hx hy hz
    , AppendX hy ty y
    , Add_ X8 (X_ hz ty) z
    ) => Add_ (X_ hx X8) y z
instance
    ( XNaturalNE0_ hx, XNatural_ z
    , Add_ hx hy hz
    , AppendX hy ty y
    , Add_ X9 (X_ hz ty) z
    ) => Add_ (X_ hx X9) y z


-- | Assert that @10*h + t == x@ where @x@ is a decimal digit. @h@
-- may be zero. Essentially, this is the general, non-structural,
-- constructor\/deconstructor of a decimal number.
class (XNatural_ h, XNatural_ x) => AppendX h t x | h t -> x, x -> h t
instance                        AppendX X0 X0 X0
instance                        AppendX X0 X1 X1
instance                        AppendX X0 X2 X2
instance                        AppendX X0 X3 X3
instance                        AppendX X0 X4 X4
instance                        AppendX X0 X5 X5
instance                        AppendX X0 X6 X6
instance                        AppendX X0 X7 X7
instance                        AppendX X0 X8 X8
instance                        AppendX X0 X9 X9
instance XNatural_ (X_ X1 t) => AppendX X1 t (X_ X1 t)
instance XNatural_ (X_ X2 t) => AppendX X2 t (X_ X2 t)
instance XNatural_ (X_ X3 t) => AppendX X3 t (X_ X3 t)
instance XNatural_ (X_ X4 t) => AppendX X4 t (X_ X4 t)
instance XNatural_ (X_ X5 t) => AppendX X5 t (X_ X5 t)
instance XNatural_ (X_ X6 t) => AppendX X6 t (X_ X6 t)
instance XNatural_ (X_ X7 t) => AppendX X7 t (X_ X7 t)
instance XNatural_ (X_ X8 t) => AppendX X8 t (X_ X8 t)
instance XNatural_ (X_ X9 t) => AppendX X9 t (X_ X9 t)
instance (XNatural_ (X_ x y), XNatural_ (X_ (X_ x y) z))
    => AppendX (X_ x y) z (X_ (X_ x y) z)


-- | The addition relation with full dependencies
class (Add_ x y z, Add_ y x z) => Add x y z | x y -> z, z x -> y, z y -> x
-- This instance is "undecidable" since GHC can't see enough
instance (Add_ x y z, Add_ y x z) => Add x y z


-- | Convert a valid @TyUnsigned@ into a valid @XNatural@.
class (TyUnsigned_ d, XNatural_ x) => D2X_ d x | d -> x
instance                                                D2X_ D_     X0
instance (TyUnsigned_' d, D2X_' d x, AppendX X1 x y) => D2X_ (D1 d) y
instance (TyUnsigned_' d, D2X_' d x, AppendX X2 x y) => D2X_ (D2 d) y
instance (TyUnsigned_' d, D2X_' d x, AppendX X3 x y) => D2X_ (D3 d) y
instance (TyUnsigned_' d, D2X_' d x, AppendX X4 x y) => D2X_ (D4 d) y
instance (TyUnsigned_' d, D2X_' d x, AppendX X5 x y) => D2X_ (D5 d) y
instance (TyUnsigned_' d, D2X_' d x, AppendX X6 x y) => D2X_ (D6 d) y
instance (TyUnsigned_' d, D2X_' d x, AppendX X7 x y) => D2X_ (D7 d) y
instance (TyUnsigned_' d, D2X_' d x, AppendX X8 x y) => D2X_ (D8 d) y
instance (TyUnsigned_' d, D2X_' d x, AppendX X9 x y) => D2X_ (D9 d) y

class (TyUnsigned_' d, XNatural_ x) => D2X_' d x | d -> x
instance                                                D2X_' D_     X0
instance                 (D2X_' d x)                 => D2X_' (D0 d) x
instance (TyUnsigned_' d, D2X_' d x, AppendX X1 x y) => D2X_' (D1 d) y
instance (TyUnsigned_' d, D2X_' d x, AppendX X2 x y) => D2X_' (D2 d) y
instance (TyUnsigned_' d, D2X_' d x, AppendX X3 x y) => D2X_' (D3 d) y
instance (TyUnsigned_' d, D2X_' d x, AppendX X4 x y) => D2X_' (D4 d) y
instance (TyUnsigned_' d, D2X_' d x, AppendX X5 x y) => D2X_' (D5 d) y
instance (TyUnsigned_' d, D2X_' d x, AppendX X6 x y) => D2X_' (D6 d) y
instance (TyUnsigned_' d, D2X_' d x, AppendX X7 x y) => D2X_' (D7 d) y
instance (TyUnsigned_' d, D2X_' d x, AppendX X8 x y) => D2X_' (D8 d) y
instance (TyUnsigned_' d, D2X_' d x, AppendX X9 x y) => D2X_' (D9 d) y

{-
-- BUG: we need something like AppendX, but for D.
class (XNatural_ x, TyUnsigned_ d) => X2D_ x d | x -> d
instance X2D_ X0 D_
instance X2D_ X1 (D1 D_)
instance X2D_ X2 (D2 D_)
instance X2D_ X3 (D3 D_)
instance X2D_ X4 (D4 D_)
instance X2D_ X5 (D5 D_)
instance X2D_ X6 (D6 D_)
instance X2D_ X7 (D7 D_)
instance X2D_ X8 (D8 D_)
instance X2D_ X9 (D9 D_)
instance (TyUnsigned_' d, AppendX X1 z (X_ x X0), X2D_ z d)
    => X2D_ (X_ x X0) (D1 d)
instance (TyUnsigned_' d, AppendX X1 z (X_ x X1), X2D_ z d)
    => X2D_ (X_ x X1) (D1 d)
instance (TyUnsigned_' d, AppendX X1 z (X_ x X2), X2D_ z d)
    => X2D_ (X_ x X2) (D1 d)
instance (TyUnsigned_' d, AppendX X1 z (X_ x X3), X2D_ z d)
    => X2D_ (X_ x X3) (D1 d)
instance (TyUnsigned_' d, AppendX X1 z (X_ x X4), X2D_ z d)
    => X2D_ (X_ x X4) (D1 d)
instance (TyUnsigned_' d, AppendX X1 z (X_ x X5), X2D_ z d)
    => X2D_ (X_ x X5) (D1 d)
instance (TyUnsigned_' d, AppendX X1 z (X_ x X6), X2D_ z d)
    => X2D_ (X_ x X6) (D1 d)
instance (TyUnsigned_' d, AppendX X1 z (X_ x X7), X2D_ z d)
    => X2D_ (X_ x X7) (D1 d)
instance (TyUnsigned_' d, AppendX X1 z (X_ x X8), X2D_ z d)
    => X2D_ (X_ x X8) (D1 d)
instance (TyUnsigned_' d, AppendX X1 z (X_ x X9), X2D_ z d)
    => X2D_ (X_ x X9) (D1 d)
-- BUG: fundep breakage...
instance (TyUnsigned_' d, AppendX X2 z (X_ x X0), X2D_ z d)
    => X2D_ (X_ x X0) (D2 d)
instance (TyUnsigned_' d, AppendX X2 z (X_ x X1), X2D_ z d)
    => X2D_ (X_ x X1) (D2 d)
instance (TyUnsigned_' d, AppendX X2 z (X_ x X2), X2D_ z d)
    => X2D_ (X_ x X2) (D2 d)
instance (TyUnsigned_' d, AppendX X2 z (X_ x X3), X2D_ z d)
    => X2D_ (X_ x X3) (D2 d)
instance (TyUnsigned_' d, AppendX X2 z (X_ x X4), X2D_ z d)
    => X2D_ (X_ x X4) (D2 d)
instance (TyUnsigned_' d, AppendX X2 z (X_ x X5), X2D_ z d)
    => X2D_ (X_ x X5) (D2 d)
instance (TyUnsigned_' d, AppendX X2 z (X_ x X6), X2D_ z d)
    => X2D_ (X_ x X6) (D2 d)
instance (TyUnsigned_' d, AppendX X2 z (X_ x X7), X2D_ z d)
    => X2D_ (X_ x X7) (D2 d)
instance (TyUnsigned_' d, AppendX X2 z (X_ x X8), X2D_ z d)
    => X2D_ (X_ x X8) (D2 d)
instance (TyUnsigned_' d, AppendX X2 z (X_ x X9), X2D_ z d)
    => X2D_ (X_ x X9) (D2 d)

instance (AppendX X2 z (X_ x y), X2D_ z d) => X2D_ (X_ x y) (D2 d)
instance (AppendX X3 z (X_ x y), X2D_ z d) => X2D_ (X_ x y) (D3 d)
instance (AppendX X4 z (X_ x y), X2D_ z d) => X2D_ (X_ x y) (D4 d)
instance (AppendX X5 z (X_ x y), X2D_ z d) => X2D_ (X_ x y) (D5 d)
instance (AppendX X6 z (X_ x y), X2D_ z d) => X2D_ (X_ x y) (D6 d)
instance (AppendX X7 z (X_ x y), X2D_ z d) => X2D_ (X_ x y) (D7 d)
instance (AppendX X8 z (X_ x y), X2D_ z d) => X2D_ (X_ x y) (D8 d)
instance (AppendX X9 z (X_ x y), X2D_ z d) => X2D_ (X_ x y) (D9 d)
-}

----------------------------------------------------------------
----------------------------------------------------------- fin.
