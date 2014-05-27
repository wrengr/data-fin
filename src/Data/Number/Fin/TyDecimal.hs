-- TODO: see also <http://okmij.org/ftp/Haskell/PeanoArithm.lhs>
{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
{-# LANGUAGE EmptyDataDecls
           , DeriveDataTypeable
           , MultiParamTypeClasses
           , FlexibleContexts
           , FlexibleInstances
           , UndecidableInstances
           , FunctionalDependencies
           , TypeOperators
           #-}
{-
-- for reifyNat...
{-# LANGUAGE RankNTypes #-}
-}

{-# LANGUAGE CPP #-}
#if __GLASGOW_HASKELL__ >= 701
-- N.B., Data.Proxy isn't "safe".
{-# LANGUAGE Trustworthy #-}
#endif
----------------------------------------------------------------
--                                                    2013.05.29
-- |
-- Module      :  Data.Number.Fin.TyDecimal
-- Copyright   :  2012--2013 wren gayle romano,
--                2004--2007 Oleg Kiselyov and Chung-chieh Shan
-- License     :  BSD3
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Type-level decimal natural numbers. This is based on [1], and is
-- intended to work with [2] (though we use the @reflection@ package
-- for the actual reification part).
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
module Data.Number.Fin.TyDecimal
    (
    -- * Representation
    -- ** Type-level decimal natural numbers
      D0, D1, D2, D3, D4, D5, D6, D7, D8, D9, (:.)
    -- ** Type-level 'Ordering'
    , LT_, EQ_, GT_
    
    -- * Kind predicates
    , Nat, NatNE0
    -- * Proxies for some small numbers
    , nat0, nat1, nat2, nat3, nat4, nat5, nat6, nat7, nat8, nat9
    -- * Aliases for some large numbers
    , MaxBoundInt8
    , MaxBoundInt16
    , MaxBoundInt32
    , MaxBoundInt64
    , MaxBoundWord8
    , MaxBoundWord16
    , MaxBoundWord32
    , MaxBoundWord64
    
    -- * Arithmetic
    -- ** successor\/predecessor
    , Succ, succ, pred
    -- ** addition\/subtraction
    , Add, add, minus, subtract
    -- ** comparison
    , Compare, compare, NatLE, NatLT, assert_NatLE, min, max
    {-
    -- ** multiplication\/division
    , Mul, mul, div, div10 -- mul10 ?
    -- ** exponentiation\/logarithm
    , Exp10, exp10, log10
    -- ** GCD
    , GCD, gcd
    -}
    ) where

import Prelude hiding  (succ, pred, subtract, compare, div, gcd, max, min)
import Data.Typeable   (Typeable)
import Data.Proxy      (Proxy(Proxy))
import Data.Reflection (Reifies(reflect))
import Data.Number.Fin.TyOrdering
----------------------------------------------------------------

-- | The digit 0.
data D0 deriving Typeable
-- | The digit 1.
data D1 deriving Typeable
-- | The digit 2.
data D2 deriving Typeable
-- | The digit 3.
data D3 deriving Typeable
-- | The digit 4.
data D4 deriving Typeable
-- | The digit 5.
data D5 deriving Typeable
-- | The digit 6.
data D6 deriving Typeable
-- | The digit 7.
data D7 deriving Typeable
-- | The digit 8.
data D8 deriving Typeable
-- | The digit 9.
data D9 deriving Typeable

-- | The connective. This should only be used left associatively
-- (it associates to the left naturally). Decimal digits are
-- lexicographically big-endian, so they're written as usual;
-- however, they're structurally little-endian due to the left
-- associativity.
data x :. y deriving Typeable
infixl 5 :.


-- | Is @n@ a well-formed type of kind @Nat@? The only well-formed
-- types of kind @Nat@ are type-level natural numbers in structurally
-- little-endian decimal.
--
-- The hidden type class @(Nat_ n)@ entails @(Reifies n Integer)@.
class    Nat_ n => Nat n
instance Nat_ n => Nat n -- this instance is "undecidable"


-- | Is @n@ a well-formed type of kind @NatNE0@? The only well-formed
-- types of kind @NatNE0@ are the non-zero well-formed types of
-- kind @Nat@;, i.e., the type-level whole numbers in structurally
-- little-endian decimal.
--
-- The hidden type class @(NatNE0_ n)@ entails @(Nat_ n)@ and
-- @(Reifies n Integer)@.
class    NatNE0_ n => NatNE0 n
instance NatNE0_ n => NatNE0 n -- this instance is "undecidable"


-- for internal use only.
class    Digit_ d
instance Digit_ D0
instance Digit_ D1
instance Digit_ D2
instance Digit_ D3
instance Digit_ D4
instance Digit_ D5
instance Digit_ D6
instance Digit_ D7
instance Digit_ D8
instance Digit_ D9

-- for internal use only.
class (Reifies n Integer, Nat_ n) => NatNE0_ n
instance              NatNE0_ D1
instance              NatNE0_ D2
instance              NatNE0_ D3
instance              NatNE0_ D4
instance              NatNE0_ D5
instance              NatNE0_ D6
instance              NatNE0_ D7
instance              NatNE0_ D8
instance              NatNE0_ D9
instance NatNE0_ n => NatNE0_ (n:.D0)
instance NatNE0_ n => NatNE0_ (n:.D1)
instance NatNE0_ n => NatNE0_ (n:.D2)
instance NatNE0_ n => NatNE0_ (n:.D3)
instance NatNE0_ n => NatNE0_ (n:.D4)
instance NatNE0_ n => NatNE0_ (n:.D5)
instance NatNE0_ n => NatNE0_ (n:.D6)
instance NatNE0_ n => NatNE0_ (n:.D7)
instance NatNE0_ n => NatNE0_ (n:.D8)
instance NatNE0_ n => NatNE0_ (n:.D9)

-- for internal use only.
class (Reifies n Integer) => Nat_ n
instance              Nat_ D0
instance              Nat_ D1
instance              Nat_ D2
instance              Nat_ D3
instance              Nat_ D4
instance              Nat_ D5
instance              Nat_ D6
instance              Nat_ D7
instance              Nat_ D8
instance              Nat_ D9
instance NatNE0_ x => Nat_ (x:.D0)
instance NatNE0_ x => Nat_ (x:.D1)
instance NatNE0_ x => Nat_ (x:.D2)
instance NatNE0_ x => Nat_ (x:.D3)
instance NatNE0_ x => Nat_ (x:.D4)
instance NatNE0_ x => Nat_ (x:.D5)
instance NatNE0_ x => Nat_ (x:.D6)
instance NatNE0_ x => Nat_ (x:.D7)
instance NatNE0_ x => Nat_ (x:.D8)
instance NatNE0_ x => Nat_ (x:.D9)


-- BUG: stack overflow issues, unlike the big-endian notation?
instance Reifies D0 Integer where reflect _ = 0 
instance Reifies D1 Integer where reflect _ = 1 
instance Reifies D2 Integer where reflect _ = 2 
instance Reifies D3 Integer where reflect _ = 3 
instance Reifies D4 Integer where reflect _ = 4 
instance Reifies D5 Integer where reflect _ = 5 
instance Reifies D6 Integer where reflect _ = 6 
instance Reifies D7 Integer where reflect _ = 7 
instance Reifies D8 Integer where reflect _ = 8 
instance Reifies D9 Integer where reflect _ = 9 
instance NatNE0_ x => Reifies (x:.D0) Integer where
    reflect p = 10 * reflect (div10 p)
instance NatNE0_ x => Reifies (x:.D1) Integer where
    reflect p = 10 * reflect (div10 p) + 1
instance NatNE0_ x => Reifies (x:.D2) Integer where
    reflect p = 10 * reflect (div10 p) + 2
instance NatNE0_ x => Reifies (x:.D3) Integer where
    reflect p = 10 * reflect (div10 p) + 3
instance NatNE0_ x => Reifies (x:.D4) Integer where
    reflect p = 10 * reflect (div10 p) + 4
instance NatNE0_ x => Reifies (x:.D5) Integer where
    reflect p = 10 * reflect (div10 p) + 5
instance NatNE0_ x => Reifies (x:.D6) Integer where
    reflect p = 10 * reflect (div10 p) + 6
instance NatNE0_ x => Reifies (x:.D7) Integer where
    reflect p = 10 * reflect (div10 p) + 7
instance NatNE0_ x => Reifies (x:.D8) Integer where
    reflect p = 10 * reflect (div10 p) + 8
instance NatNE0_ x => Reifies (x:.D9) Integer where
    reflect p = 10 * reflect (div10 p) + 9

-- HACK: we can't actually monomorphize the input, given our use case.
-- | Return a 'Proxy' for the floor of the input divided by 10. Using
-- @div10 n@ differs from using @n \`div\` nat10@ in that we take the
-- floor of the result rather than being ill-typed; also in that
-- @div10@ isn't defined on single-digit numbers.
div10 :: proxy (h:.t) -> Proxy h
div10 _ = Proxy
{-# INLINE div10 #-}


{-
-- BUG: how can we do this CPS version which properly constrains @x@ to Nat_? It wasn't so hard with the big-endian notation...
reifyNat :: Integer -> (forall x. Nat_ x => Proxy x -> r) -> r
reifyNat i k
    | i <= 0    = k (Proxy :: Proxy D0)
    | otherwise =
        let (d,m) = divMod i 10 in
        case m of
        0 -> reifyNat d (\p -> k (snoc p (Proxy :: Proxy D0)))
        1 -> reifyNat d (\p -> k (snoc p (Proxy :: Proxy D1)))
        2 -> reifyNat d (\p -> k (snoc p (Proxy :: Proxy D2)))
        3 -> reifyNat d (\p -> k (snoc p (Proxy :: Proxy D3)))
        4 -> reifyNat d (\p -> k (snoc p (Proxy :: Proxy D4)))
        5 -> reifyNat d (\p -> k (snoc p (Proxy :: Proxy D5)))
        6 -> reifyNat d (\p -> k (snoc p (Proxy :: Proxy D6)))
        7 -> reifyNat d (\p -> k (snoc p (Proxy :: Proxy D7)))
        8 -> reifyNat d (\p -> k (snoc p (Proxy :: Proxy D8)))
        9 -> reifyNat d (\p -> k (snoc p (Proxy :: Proxy D9)))
        _ -> error "Data.Number.Fin.TyDecimal.reifyNat: the impossible happened"
    where
    -- BUG: Could not deduce (Snoc x10 D0 x) from the context (Nat_ x10) [etc]
    snoc :: Snoc x d y => Proxy x -> Proxy d -> Proxy y
    snoc _ _ = Proxy
-}



nat0 :: Proxy D0; nat0 = Proxy 
nat1 :: Proxy D1; nat1 = Proxy 
nat2 :: Proxy D2; nat2 = Proxy 
nat3 :: Proxy D3; nat3 = Proxy 
nat4 :: Proxy D4; nat4 = Proxy 
nat5 :: Proxy D5; nat5 = Proxy 
nat6 :: Proxy D6; nat6 = Proxy 
nat7 :: Proxy D7; nat7 = Proxy 
nat8 :: Proxy D8; nat8 = Proxy 
nat9 :: Proxy D9; nat9 = Proxy 


-- type MinBoundInt8  = Negative (D1:.D2:.D8)
-- type MinBoundInt16 = Negative (D3:.D2:. D7:.D6:.D8)
-- type MinBoundInt32 = Negative (D2:. D1:.D4:.D7:. D4:.D8:.D3:. D6:.D4:.D8)
-- type MinBoundInt64 =
--     Negative (D9:. D2:.D2:.D3:. D3:.D7:.D2:. D0:.D3:.D6:. D8:.D5:.D4:. D7:.D7:.D5:. D8:.D0:.D8)
-- TODO: MinBoundInt

type MaxBoundInt8  = D1:.D2:.D7 
type MaxBoundInt16 = D3:.D2:.D7:.D6:.D7 
type MaxBoundInt32 = D2:.D1:.D4:.D7:.D4:.D8:.D3:.D6:.D4:.D7 
type MaxBoundInt64 =
    D9:.D2:.D2:.D3:.D3:.D7:.D2:.D0:.D3:.D6:.D8:.D5:.D4:.D7:.D7:.D5:.D8:.D0:.D7 
-- TODO: MaxBoundInt

type MaxBoundWord8  = D2:.D5:.D5 
type MaxBoundWord16 = D6:.D5:.D5:.D3:.D5 
type MaxBoundWord32 = D4:.D2:.D9:.D4:.D9:.D6:.D7:.D2:.D9:.D5 
type MaxBoundWord64 =
    D1:.D8:.D4:.D4:.D6:.D7:.D4:.D4:.D0:.D7:.D3:.D7:.D0:.D9:.D5:.D5:.D1:.D6:.D1:.D5 
-- TODO: MaxBoundWord


----------------------------------------------------------------
-- BUG: We can't automatically deduce (NatLE x y) nor (NatLT x y) from (Succ x y). We can add them as additional constraints on the instances; and that works to get everything in this package to typecheck, but it causes infinite loops whenever we actually try to use Succ as a type-function in real code...

-- | The successor\/predecessor relation; by structural induction
-- on the first argument. Modes:
--
-- > Succ x (succ x)  -- i.e., given x, return the successor of x
-- > Succ (pred y) y  -- i.e., given y, return the predecessor of y
--
class (Nat_ x, NatNE0_ y) => Succ x y | x -> y, y -> x
instance                               Succ D0      D1
instance                               Succ D1      D2
instance                               Succ D2      D3
instance                               Succ D3      D4
instance                               Succ D4      D5
instance                               Succ D5      D6
instance                               Succ D6      D7
instance                               Succ D7      D8
instance                               Succ D8      D9
instance                               Succ D9      (D1:.D0)
instance (NatNE0_ x)                => Succ (x:.D0) (x :.D1)
instance (NatNE0_ x)                => Succ (x:.D1) (x :.D2)
instance (NatNE0_ x)                => Succ (x:.D2) (x :.D3)
instance (NatNE0_ x)                => Succ (x:.D3) (x :.D4)
instance (NatNE0_ x)                => Succ (x:.D4) (x :.D5)
instance (NatNE0_ x)                => Succ (x:.D5) (x :.D6)
instance (NatNE0_ x)                => Succ (x:.D6) (x :.D7)
instance (NatNE0_ x)                => Succ (x:.D7) (x :.D8)
instance (NatNE0_ x)                => Succ (x:.D8) (x :.D9)
instance (NatNE0_ x, Succ x (y:.d)) => Succ (x:.D9) (y :.d :.D0)
-- this last case triggers the need for undecidable instances <sigh>

succ :: Succ x y => Proxy x -> Proxy y
succ _ = Proxy
{-# INLINE succ #-}

pred :: Succ x y => Proxy y -> Proxy x
pred _ = Proxy
{-# INLINE pred #-}


-- | Assert @10*x + d == y@ where @d@ is a decimal digit and both @x@
-- and @y@ are decimal numbers. @x@ may be zero. Essentially, this
-- is the general, non-structural, constructor\/deconstructor of a
-- decimal number. This is like the assertion @x:.d ~ y@ except that
-- we trim leading zeros of @y@ in order to ensure that it is
-- well-formed.
class (Digit_ d, Nat_ x, Nat_ y) => Snoc x d y | x d -> y, y -> x d
instance                                              Snoc D0     D0 D0
instance                                              Snoc D0     D1 D1
instance                                              Snoc D0     D2 D2
instance                                              Snoc D0     D3 D3
instance                                              Snoc D0     D4 D4
instance                                              Snoc D0     D5 D5
instance                                              Snoc D0     D6 D6
instance                                              Snoc D0     D7 D7
instance                                              Snoc D0     D8 D8
instance                                              Snoc D0     D9 D9
instance (Digit_ d,  Nat_ (D1:.d))                 => Snoc D1     d  (D1:.d)
instance (Digit_ d,  Nat_ (D2:.d))                 => Snoc D2     d  (D2:.d)
instance (Digit_ d,  Nat_ (D3:.d))                 => Snoc D3     d  (D3:.d)
instance (Digit_ d,  Nat_ (D4:.d))                 => Snoc D4     d  (D4:.d)
instance (Digit_ d,  Nat_ (D5:.d))                 => Snoc D5     d  (D5:.d)
instance (Digit_ d,  Nat_ (D6:.d))                 => Snoc D6     d  (D6:.d)
instance (Digit_ d,  Nat_ (D7:.d))                 => Snoc D7     d  (D7:.d)
instance (Digit_ d,  Nat_ (D8:.d))                 => Snoc D8     d  (D8:.d)
instance (Digit_ d,  Nat_ (D9:.d))                 => Snoc D9     d  (D9:.d)
instance (Digit_ d', Nat_ (x:.d), Nat_ (x:.d:.d')) => Snoc (x:.d) d' (x:.d:.d')


-- | The primitive addition relation; by structural induction on
-- the first argument. Modes:
--
-- > Add_ x y (x+y)
-- > Add_ x (z-x) z  -- when it's defined.
--
class (Nat_ x, Nat_ y, Nat_ z) => Add_ x y z | x y -> z, z x -> y
instance (Nat_ y)                            => Add_ D0 y y
instance (Succ y y1)                         => Add_ D1 y y1
instance (Succ y y1, Succ y1 y2)             => Add_ D2 y y2
instance (Succ y y1, Succ y1 y2, Succ y2 y3) => Add_ D3 y y3
instance
    ( Succ y  y1, Succ y1 y2, Succ y2 y3
    , Succ y3 y4
    ) => Add_ D4 y y4
instance
    ( Succ y  y1, Succ y1 y2, Succ y2 y3
    , Succ y3 y4, Succ y4 y5
    ) => Add_ D5 y y5
instance
    ( Succ y  y1, Succ y1 y2, Succ y2 y3
    , Succ y3 y4, Succ y4 y5, Succ y5 y6
    ) => Add_ D6 y y6
instance
    ( Succ y  y1, Succ y1 y2, Succ y2 y3
    , Succ y3 y4, Succ y4 y5, Succ y5 y6
    , Succ y6 y7
    ) => Add_ D7 y y7
instance
    ( Succ y  y1, Succ y1 y2, Succ y2 y3
    , Succ y3 y4, Succ y4 y5, Succ y5 y6
    , Succ y6 y7, Succ y7 y8
    ) => Add_ D8 y y8
instance
    ( Succ y  y1, Succ y1 y2, Succ y2 y3
    , Succ y3 y4, Succ y4 y5, Succ y5 y6
    , Succ y6 y7, Succ y7 y8, Succ y8 y9
    ) => Add_ D9 y y9
instance (NatNE0_ x, NatNE0_ (z:.dz), Add_ x y' z, Snoc y' dz y)
    => Add_ (x:.D0) y (z:.dz)
instance (NatNE0_ x, Nat_ z, Add_ x y' zh, Snoc y' dy y, Add_ D1 (zh:.dy) z)
    => Add_ (x:.D1) y z
instance (NatNE0_ x, Nat_ z, Add_ x y' zh, Snoc y' dy y, Add_ D2 (zh:.dy) z)
    => Add_ (x:.D2) y z
instance (NatNE0_ x, Nat_ z, Add_ x y' zh, Snoc y' dy y, Add_ D3 (zh:.dy) z)
    => Add_ (x:.D3) y z
instance (NatNE0_ x, Nat_ z, Add_ x y' zh, Snoc y' dy y, Add_ D4 (zh:.dy) z)
    => Add_ (x:.D4) y z
instance (NatNE0_ x, Nat_ z, Add_ x y' zh, Snoc y' dy y, Add_ D5 (zh:.dy) z)
    => Add_ (x:.D5) y z
instance (NatNE0_ x, Nat_ z, Add_ x y' zh, Snoc y' dy y, Add_ D6 (zh:.dy) z)
    => Add_ (x:.D6) y z
instance (NatNE0_ x, Nat_ z, Add_ x y' zh, Snoc y' dy y, Add_ D7 (zh:.dy) z)
    => Add_ (x:.D7) y z
instance (NatNE0_ x, Nat_ z, Add_ x y' zh, Snoc y' dy y, Add_ D8 (zh:.dy) z)
    => Add_ (x:.D8) y z
instance (NatNE0_ x, Nat_ z, Add_ x y' zh, Snoc y' dy y, Add_ D9 (zh:.dy) z)
    => Add_ (x:.D9) y z


-- | The addition relation with full dependencies. Modes:
--
-- > Add x y (x+y)
-- > Add x (z-x) z  -- when it's defined.
-- > Add (z-y) y z  -- when it's defined.
--
class    (Add_ x y z, Add_ y x z) => Add x y z | x y -> z, z x -> y, z y -> x
instance (Add_ x y z, Add_ y x z) => Add x y z

add :: Add x y z => Proxy x -> Proxy y -> Proxy z
add _ _ = Proxy
{-# INLINE add #-}

-- | N.B., this will be ill-typed if @x@ is greater than @z@.
minus :: Add x y z => Proxy z -> Proxy x -> Proxy y
minus _ _ = Proxy
{-# INLINE minus #-}

-- | N.B., this will be ill-typed if @x@ is greater than @z@.
subtract :: Add x y z => Proxy x -> Proxy z -> Proxy y
subtract _ _ = Proxy
{-# INLINE subtract #-}

----------------------------------------------------------------
-- Equality and order: the comparison relation

-- | Assert that the comparison relation @r@ (@LT_@, @EQ_@, or
-- @GT_@) holds between @x@ and @y@; by structural induction on the
-- first, and then the second argument.
class   (Nat_ x, Nat_ y) => Compare x y r | x y -> r
instance                    Compare D0 D0      EQ_
instance                    Compare D0 D1      LT_
instance                    Compare D0 D2      LT_
instance                    Compare D0 D3      LT_
instance                    Compare D0 D4      LT_
instance                    Compare D0 D5      LT_
instance                    Compare D0 D6      LT_
instance                    Compare D0 D7      LT_
instance                    Compare D0 D8      LT_
instance                    Compare D0 D9      LT_
instance NatNE0_ (y:.dy) => Compare D0 (y:.dy) LT_
instance                    Compare D1 D0      GT_
instance                    Compare D1 D1      EQ_
instance                    Compare D1 D2      LT_
instance                    Compare D1 D3      LT_
instance                    Compare D1 D4      LT_
instance                    Compare D1 D5      LT_
instance                    Compare D1 D6      LT_
instance                    Compare D1 D7      LT_
instance                    Compare D1 D8      LT_
instance                    Compare D1 D9      LT_
instance NatNE0_ (y:.dy) => Compare D1 (y:.dy) LT_
instance                    Compare D2 D0      GT_
instance                    Compare D2 D1      GT_
instance                    Compare D2 D2      EQ_
instance                    Compare D2 D3      LT_
instance                    Compare D2 D4      LT_
instance                    Compare D2 D5      LT_
instance                    Compare D2 D6      LT_
instance                    Compare D2 D7      LT_
instance                    Compare D2 D8      LT_
instance                    Compare D2 D9      LT_
instance NatNE0_ (y:.dy) => Compare D2 (y:.dy) LT_
instance                    Compare D3 D0      GT_
instance                    Compare D3 D1      GT_
instance                    Compare D3 D2      GT_
instance                    Compare D3 D3      EQ_
instance                    Compare D3 D4      LT_
instance                    Compare D3 D5      LT_
instance                    Compare D3 D6      LT_
instance                    Compare D3 D7      LT_
instance                    Compare D3 D8      LT_
instance                    Compare D3 D9      LT_
instance NatNE0_ (y:.dy) => Compare D3 (y:.dy) LT_
instance                    Compare D4 D0      GT_
instance                    Compare D4 D1      GT_
instance                    Compare D4 D2      GT_
instance                    Compare D4 D3      GT_
instance                    Compare D4 D4      EQ_
instance                    Compare D4 D5      LT_
instance                    Compare D4 D6      LT_
instance                    Compare D4 D7      LT_
instance                    Compare D4 D8      LT_
instance                    Compare D4 D9      LT_
instance NatNE0_ (y:.dy) => Compare D4 (y:.dy) LT_
instance                    Compare D5 D0      GT_
instance                    Compare D5 D1      GT_
instance                    Compare D5 D2      GT_
instance                    Compare D5 D3      GT_
instance                    Compare D5 D4      GT_
instance                    Compare D5 D5      EQ_
instance                    Compare D5 D6      LT_
instance                    Compare D5 D7      LT_
instance                    Compare D5 D8      LT_
instance                    Compare D5 D9      LT_
instance NatNE0_ (y:.dy) => Compare D5 (y:.dy) LT_
instance                    Compare D6 D0      GT_
instance                    Compare D6 D1      GT_
instance                    Compare D6 D2      GT_
instance                    Compare D6 D3      GT_
instance                    Compare D6 D4      GT_
instance                    Compare D6 D5      GT_
instance                    Compare D6 D6      EQ_
instance                    Compare D6 D7      LT_
instance                    Compare D6 D8      LT_
instance                    Compare D6 D9      LT_
instance NatNE0_ (y:.dy) => Compare D6 (y:.dy) LT_
instance                    Compare D7 D0      GT_
instance                    Compare D7 D1      GT_
instance                    Compare D7 D2      GT_
instance                    Compare D7 D3      GT_
instance                    Compare D7 D4      GT_
instance                    Compare D7 D5      GT_
instance                    Compare D7 D6      GT_
instance                    Compare D7 D7      EQ_
instance                    Compare D7 D8      LT_
instance                    Compare D7 D9      LT_
instance NatNE0_ (y:.dy) => Compare D7 (y:.dy) LT_
instance                    Compare D8 D0      GT_
instance                    Compare D8 D1      GT_
instance                    Compare D8 D2      GT_
instance                    Compare D8 D3      GT_
instance                    Compare D8 D4      GT_
instance                    Compare D8 D5      GT_
instance                    Compare D8 D6      GT_
instance                    Compare D8 D7      GT_
instance                    Compare D8 D8      EQ_
instance                    Compare D8 D9      LT_
instance NatNE0_ (y:.dy) => Compare D8 (y:.dy) LT_
instance                    Compare D9 D0      GT_
instance                    Compare D9 D1      GT_
instance                    Compare D9 D2      GT_
instance                    Compare D9 D3      GT_
instance                    Compare D9 D4      GT_
instance                    Compare D9 D5      GT_
instance                    Compare D9 D6      GT_
instance                    Compare D9 D7      GT_
instance                    Compare D9 D8      GT_
instance                    Compare D9 D9      EQ_
instance NatNE0_ (y:.dy) => Compare D9 (y:.dy) LT_
instance NatNE0_ (x:.dx) => Compare (x:.dx) D0 GT_
instance NatNE0_ (x:.dx) => Compare (x:.dx) D1 GT_
instance NatNE0_ (x:.dx) => Compare (x:.dx) D2 GT_
instance NatNE0_ (x:.dx) => Compare (x:.dx) D3 GT_
instance NatNE0_ (x:.dx) => Compare (x:.dx) D4 GT_
instance NatNE0_ (x:.dx) => Compare (x:.dx) D5 GT_
instance NatNE0_ (x:.dx) => Compare (x:.dx) D6 GT_
instance NatNE0_ (x:.dx) => Compare (x:.dx) D7 GT_
instance NatNE0_ (x:.dx) => Compare (x:.dx) D8 GT_
instance NatNE0_ (x:.dx) => Compare (x:.dx) D9 GT_
instance
    ( NatNE0_ (x:.dx), NatNE0_ (y:.dy)
    , Compare dx dy dr, Compare x y r', NCS r' dr r
    ) => Compare (x:.dx) (y:.dy) r

compare :: Compare x y r => Proxy x -> Proxy y -> Proxy r
compare _ _ = Proxy
{-# INLINE compare #-}


-- BUG: is this still an optimization now that there's a combinatorial explosion?
-- | Assert that @x <= y@. This is a popular constraint, so we
-- implement it specially. We could have said that @Add n x y =>
-- NatLE x y@, but the following inductive definition is a bit
-- more optimal.
class (Nat_ x, Nat_ y) => NatLE x y
instance                                            NatLE D0 D0
instance                                            NatLE D0 D1
instance                                            NatLE D0 D2
instance                                            NatLE D0 D3
instance                                            NatLE D0 D4
instance                                            NatLE D0 D5
instance                                            NatLE D0 D6
instance                                            NatLE D0 D7
instance                                            NatLE D0 D8
instance                                            NatLE D0 D9
instance NatNE0_ (y:.dy)                         => NatLE D0 (y:.dy)
instance                                            NatLE D1 D1
instance                                            NatLE D1 D2
instance                                            NatLE D1 D3
instance                                            NatLE D1 D4
instance                                            NatLE D1 D5
instance                                            NatLE D1 D6
instance                                            NatLE D1 D7
instance                                            NatLE D1 D8
instance                                            NatLE D1 D9
instance NatNE0_ (y:.dy)                         => NatLE D1 (y:.dy)
instance                                            NatLE D2 D2
instance                                            NatLE D2 D3
instance                                            NatLE D2 D4
instance                                            NatLE D2 D5
instance                                            NatLE D2 D6
instance                                            NatLE D2 D7
instance                                            NatLE D2 D8
instance                                            NatLE D2 D9
instance NatNE0_ (y:.dy)                         => NatLE D2 (y:.dy)
instance                                            NatLE D3 D3
instance                                            NatLE D3 D4
instance                                            NatLE D3 D5
instance                                            NatLE D3 D6
instance                                            NatLE D3 D7
instance                                            NatLE D3 D8
instance                                            NatLE D3 D9
instance NatNE0_ (y:.dy)                         => NatLE D3 (y:.dy)
instance                                            NatLE D4 D4
instance                                            NatLE D4 D5
instance                                            NatLE D4 D6
instance                                            NatLE D4 D7
instance                                            NatLE D4 D8
instance                                            NatLE D4 D9
instance NatNE0_ (y:.dy)                         => NatLE D4 (y:.dy)
instance                                            NatLE D5 D5
instance                                            NatLE D5 D6
instance                                            NatLE D5 D7
instance                                            NatLE D5 D8
instance                                            NatLE D5 D9
instance NatNE0_ (y:.dy)                         => NatLE D5 (y:.dy)
instance                                            NatLE D6 D6
instance                                            NatLE D6 D7
instance                                            NatLE D6 D8
instance                                            NatLE D6 D9
instance NatNE0_ (y:.dy)                         => NatLE D6 (y:.dy)
instance                                            NatLE D7 D7
instance                                            NatLE D7 D8
instance                                            NatLE D7 D9
instance NatNE0_ (y:.dy)                         => NatLE D7 (y:.dy)
instance                                            NatLE D8 D8
instance                                            NatLE D8 D9
instance NatNE0_ (y:.dy)                         => NatLE D8 (y:.dy)
instance                                            NatLE D9 D9
instance NatNE0_ (y:.dy)                         => NatLE D9 (y:.dy)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)       => NatLE (x:.D0) (y:.D0)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)       => NatLE (x:.D0) (y:.D1)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)       => NatLE (x:.D0) (y:.D2)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)       => NatLE (x:.D0) (y:.D3)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)       => NatLE (x:.D0) (y:.D4)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)       => NatLE (x:.D0) (y:.D5)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)       => NatLE (x:.D0) (y:.D6)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)       => NatLE (x:.D0) (y:.D7)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)       => NatLE (x:.D0) (y:.D8)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)       => NatLE (x:.D0) (y:.D9)
instance (NatNE0_ x, NatNE0_ y, Compare x y LT_) => NatLE (x:.D1) (y:.D0)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)       => NatLE (x:.D1) (y:.D1)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)       => NatLE (x:.D1) (y:.D2)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)       => NatLE (x:.D1) (y:.D3)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)       => NatLE (x:.D1) (y:.D4)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)       => NatLE (x:.D1) (y:.D5)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)       => NatLE (x:.D1) (y:.D6)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)       => NatLE (x:.D1) (y:.D7)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)       => NatLE (x:.D1) (y:.D8)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)       => NatLE (x:.D1) (y:.D9)
instance (NatNE0_ x, NatNE0_ y, Compare x y LT_) => NatLE (x:.D2) (y:.D0)
instance (NatNE0_ x, NatNE0_ y, Compare x y LT_) => NatLE (x:.D2) (y:.D1)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)       => NatLE (x:.D2) (y:.D2)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)       => NatLE (x:.D2) (y:.D3)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)       => NatLE (x:.D2) (y:.D4)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)       => NatLE (x:.D2) (y:.D5)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)       => NatLE (x:.D2) (y:.D6)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)       => NatLE (x:.D2) (y:.D7)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)       => NatLE (x:.D2) (y:.D8)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)       => NatLE (x:.D2) (y:.D9)
instance (NatNE0_ x, NatNE0_ y, Compare x y LT_) => NatLE (x:.D3) (y:.D0)
instance (NatNE0_ x, NatNE0_ y, Compare x y LT_) => NatLE (x:.D3) (y:.D1)
instance (NatNE0_ x, NatNE0_ y, Compare x y LT_) => NatLE (x:.D3) (y:.D2)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)       => NatLE (x:.D3) (y:.D3)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)       => NatLE (x:.D3) (y:.D4)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)       => NatLE (x:.D3) (y:.D5)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)       => NatLE (x:.D3) (y:.D6)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)       => NatLE (x:.D3) (y:.D7)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)       => NatLE (x:.D3) (y:.D8)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)       => NatLE (x:.D3) (y:.D9)
instance (NatNE0_ x, NatNE0_ y, Compare x y LT_) => NatLE (x:.D4) (y:.D0)
instance (NatNE0_ x, NatNE0_ y, Compare x y LT_) => NatLE (x:.D4) (y:.D1)
instance (NatNE0_ x, NatNE0_ y, Compare x y LT_) => NatLE (x:.D4) (y:.D2)
instance (NatNE0_ x, NatNE0_ y, Compare x y LT_) => NatLE (x:.D4) (y:.D3)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)       => NatLE (x:.D4) (y:.D4)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)       => NatLE (x:.D4) (y:.D5)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)       => NatLE (x:.D4) (y:.D6)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)       => NatLE (x:.D4) (y:.D7)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)       => NatLE (x:.D4) (y:.D8)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)       => NatLE (x:.D4) (y:.D9)
instance (NatNE0_ x, NatNE0_ y, Compare x y LT_) => NatLE (x:.D5) (y:.D0)
instance (NatNE0_ x, NatNE0_ y, Compare x y LT_) => NatLE (x:.D5) (y:.D1)
instance (NatNE0_ x, NatNE0_ y, Compare x y LT_) => NatLE (x:.D5) (y:.D2)
instance (NatNE0_ x, NatNE0_ y, Compare x y LT_) => NatLE (x:.D5) (y:.D3)
instance (NatNE0_ x, NatNE0_ y, Compare x y LT_) => NatLE (x:.D5) (y:.D4)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)       => NatLE (x:.D5) (y:.D5)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)       => NatLE (x:.D5) (y:.D6)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)       => NatLE (x:.D5) (y:.D7)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)       => NatLE (x:.D5) (y:.D8)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)       => NatLE (x:.D5) (y:.D9)
instance (NatNE0_ x, NatNE0_ y, Compare x y LT_) => NatLE (x:.D6) (y:.D0)
instance (NatNE0_ x, NatNE0_ y, Compare x y LT_) => NatLE (x:.D6) (y:.D1)
instance (NatNE0_ x, NatNE0_ y, Compare x y LT_) => NatLE (x:.D6) (y:.D2)
instance (NatNE0_ x, NatNE0_ y, Compare x y LT_) => NatLE (x:.D6) (y:.D3)
instance (NatNE0_ x, NatNE0_ y, Compare x y LT_) => NatLE (x:.D6) (y:.D4)
instance (NatNE0_ x, NatNE0_ y, Compare x y LT_) => NatLE (x:.D6) (y:.D5)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)       => NatLE (x:.D6) (y:.D6)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)       => NatLE (x:.D6) (y:.D7)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)       => NatLE (x:.D6) (y:.D8)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)       => NatLE (x:.D6) (y:.D9)
instance (NatNE0_ x, NatNE0_ y, Compare x y LT_) => NatLE (x:.D7) (y:.D0)
instance (NatNE0_ x, NatNE0_ y, Compare x y LT_) => NatLE (x:.D7) (y:.D1)
instance (NatNE0_ x, NatNE0_ y, Compare x y LT_) => NatLE (x:.D7) (y:.D2)
instance (NatNE0_ x, NatNE0_ y, Compare x y LT_) => NatLE (x:.D7) (y:.D3)
instance (NatNE0_ x, NatNE0_ y, Compare x y LT_) => NatLE (x:.D7) (y:.D4)
instance (NatNE0_ x, NatNE0_ y, Compare x y LT_) => NatLE (x:.D7) (y:.D5)
instance (NatNE0_ x, NatNE0_ y, Compare x y LT_) => NatLE (x:.D7) (y:.D6)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)       => NatLE (x:.D7) (y:.D7)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)       => NatLE (x:.D7) (y:.D8)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)       => NatLE (x:.D7) (y:.D9)
instance (NatNE0_ x, NatNE0_ y, Compare x y LT_) => NatLE (x:.D8) (y:.D0)
instance (NatNE0_ x, NatNE0_ y, Compare x y LT_) => NatLE (x:.D8) (y:.D1)
instance (NatNE0_ x, NatNE0_ y, Compare x y LT_) => NatLE (x:.D8) (y:.D2)
instance (NatNE0_ x, NatNE0_ y, Compare x y LT_) => NatLE (x:.D8) (y:.D3)
instance (NatNE0_ x, NatNE0_ y, Compare x y LT_) => NatLE (x:.D8) (y:.D4)
instance (NatNE0_ x, NatNE0_ y, Compare x y LT_) => NatLE (x:.D8) (y:.D5)
instance (NatNE0_ x, NatNE0_ y, Compare x y LT_) => NatLE (x:.D8) (y:.D6)
instance (NatNE0_ x, NatNE0_ y, Compare x y LT_) => NatLE (x:.D8) (y:.D7)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)       => NatLE (x:.D8) (y:.D8)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)       => NatLE (x:.D8) (y:.D9)
instance (NatNE0_ x, NatNE0_ y, Compare x y LT_) => NatLE (x:.D9) (y:.D0)
instance (NatNE0_ x, NatNE0_ y, Compare x y LT_) => NatLE (x:.D9) (y:.D1)
instance (NatNE0_ x, NatNE0_ y, Compare x y LT_) => NatLE (x:.D9) (y:.D2)
instance (NatNE0_ x, NatNE0_ y, Compare x y LT_) => NatLE (x:.D9) (y:.D3)
instance (NatNE0_ x, NatNE0_ y, Compare x y LT_) => NatLE (x:.D9) (y:.D4)
instance (NatNE0_ x, NatNE0_ y, Compare x y LT_) => NatLE (x:.D9) (y:.D5)
instance (NatNE0_ x, NatNE0_ y, Compare x y LT_) => NatLE (x:.D9) (y:.D6)
instance (NatNE0_ x, NatNE0_ y, Compare x y LT_) => NatLE (x:.D9) (y:.D7)
instance (NatNE0_ x, NatNE0_ y, Compare x y LT_) => NatLE (x:.D9) (y:.D8)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)       => NatLE (x:.D9) (y:.D9)


-- | N.B., this will be ill-typed if @x@ is greater than @y@.
assert_NatLE :: NatLE x y => Proxy x -> Proxy y -> ()
assert_NatLE Proxy Proxy = ()


-- | Assert that @x < y@. This is just a shorthand for @x <= pred y@.
class        (Nat_ x, NatNE0_ y) => NatLT x y
instance (Succ y' y, NatLE x y') => NatLT x y


-- | Choose the larger of @x@ and @y@ according to the order @r@.
class    Max_ x y r   z | x y r -> z
instance Max_ x y LT_ y
instance Max_ x y EQ_ y -- doesn't matter which we pick
instance Max_ x y GT_ x

-- | Choose the larger of @x@ and @y@.
max :: (Compare x y r, Max_ x y r z) => Proxy x -> Proxy y -> Proxy z
max _ _ = Proxy
{-# INLINE max #-}


-- | Choose the smaller of @x@ and @y@ according to the order @r@.
class    Min_ x y r   z | x y r -> z
instance Min_ x y LT_ x
instance Min_ x y EQ_ x -- doesn't matter which we pick
instance Min_ x y GT_ y

-- | Choose the smaller of @x@ and @y@.
min :: (Compare x y r, Min_ x y r z) => Proxy x -> Proxy y -> Proxy z
min _ _ = Proxy
{-# INLINE min #-}


{-
----------------------------------------------------------------
-- TODO: should we offer @((floor.). div)@, @((ceiling.). div)@, @divMod@ ?


-- | Assert that @x * y == z@ where @x > 0@; by structural induction
-- on the first argument.
class    (NatNE0_ x, Nat_ y, Nat_ z) => Mul_ x y z | x y -> z, x z -> y
instance Nat_ y                      => Mul_ B1 y y
instance (Mul_ x y zh, Snoc zh B0 z) => Mul_ (x:.B0) y z
instance (Mul_F x y z, Mul_B x y z)  => Mul_ (x:.B1) y z


-- | Assert that @(2x+1) * y == z@ where @x > 0@.
class (NatNE0_ x, Nat_ y, Nat_ z) => Mul_F x y z | x y -> z
instance NatNE0_ x => Mul_F x B0 B0
instance NatNE0_ x => Mul_F x B1 (x:.B1)
-- (2x+1) * 2y
instance (Mul_F x y z, NatNE0_ x, NatNE0_ y, NatNE0_ z)
    => Mul_F x (y:.B0) (z:.B0)
-- (2x+1) * (2y+1) = 2*( (2x+1)*y + x ) + 1, y > 0
instance (Mul_F x y z', Add x z' z, NatNE0_ x, NatNE0_ y, NatNE0_ z)
    => Mul_F x (y:.B1) (z:.B1)


-- | Assert that @(2x+1) * y == z@ where @x > 0@. The functional
-- dependencies go the other way though.
class (NatNE0_ x, Nat_ y, Nat_ z) => Mul_B x y z | z x -> y
instance NatNE0_ x => Mul_B x B0 B0
-- instance NatNE0_ x => Mul_B x y B1 -- cannot happen
-- (2x+1) * 2y
instance (Mul_B x y z, NatNE0_ x, NatNE0_ y, NatNE0_ z)
    => Mul_B x (y:.B0) (z:.B0)
-- (2x+1) * (2y+1) = 2*( (2x+1)*y + x ) + 1, y >= 0
instance (Snoc y B1 yt, Mul_B x y z', Add x z' z, NatNE0_ x, NatNE0_ z)
    => Mul_B x yt (z:.B1)


-- | The multiplication relation with full dependencies. Modes:
--
-- > Mul x y (x*y)
-- > Mul x (z/x) z -- when it's defined.
-- > Mul (z/y) y z -- when it's defined.
--
class    (Mul_ x y z, Mul_ y x z) => Mul x y z | x y -> z, x z -> y, y z -> x
instance (Mul_ x y z, Mul_ y x z) => Mul x y z

mul :: Mul x y z => Proxy x -> Proxy y -> Proxy z
mul _ _ = Proxy
{-# INLINE mul #-}

-- | N.B., this will be ill-typed if @z@ is not a multiple of @x@.
div :: Mul x y z => Proxy z -> Proxy x -> Proxy y
div _ _ = Proxy
{-# INLINE div #-}

-- tm1 = mul nat2 nat8
-- tm2 = reflect $ mul nat8 nat2
-- tm3 = reflect $ mul (succ nat2) nat2
-- tm4 = reflect $ mul nat2 (succ nat2)
-- tm5 = reflect $ mul (succ nat4) (succ nat2)
-- tm6 = reflect $ mul (succ nat2) (succ nat4)
-- tm7 = reflect $ div (mul (succ nat8) nat2) (succ nat2) -- 18/3


----------------------------------------------------------------
-- TODO: should we offer @(floor . logBase 2)@ and @(ceiling . logBase 2)@ ?
-- TODO: general exponentiation/logarithm


-- | Power-of-two exponentiation\/logarithm relation. Modes:
--
-- > Exp2 x (2^x)
-- > Exp2 (logBase 2 y) y -- when it's defined.
--
class (Nat_ x, NatNE0_ y) => Exp2 x y | x -> y, y -> x
instance                                      Exp2 B0 B1
instance                                      Exp2 B1 (B1:.B0)
instance (Succ x1 (x:.d), Exp2 x1 (y:.B0)) => Exp2 (x:.d) (y:.B0:.B0)

exp2 :: Exp2 x y => Proxy x -> Proxy y
exp2 _ = Proxy
{-# INLINE exp2 #-}

-- | N.B., this will be ill-typed if @y@ is not a power of 2.
log2 :: Exp2 x y => Proxy y -> Proxy x
log2 _ = Proxy
{-# INLINE log2 #-}

-- te1  = exp2 (succ (succ nat8))
-- te1' = reflect $ exp2 (succ (succ nat8))
-- te2  = reflect $ log2 nat8


----------------------------------------------------------------
-- Do we need the full dependency? If we know x and we know z,
-- we can't tell what y exactly (except being the multiple of z)

-- | Get the gcd by Euclid's algorithm. Modes:
--
-- > GCD x y (gcd x y)
--
class (Nat_ x, Nat_ y, Nat_ z) => GCD x y z | x y -> z
instance Nat_ y                                    => GCD B0 y y
instance Nat_ y                                    => GCD B1 y B1
instance (Compare (x:.dx) y r, GCD_ r (x:.dx) y z) => GCD (x:.dx) y z

class (NatNE0_ x, Nat_ y, Nat_ z) => GCD_ r x y z | r x y -> z
instance NatNE0_ x                           => GCD_ EQ_ x x x
instance (GCD y x z, NatNE0_ x)              => GCD_ GT_ x y z
instance (Add x y1 y, GCD y1 x z, NatNE0_ x) => GCD_ LT_ x y z

gcd :: GCD x y z => Proxy x -> Proxy y -> Proxy z
gcd _ _ = Proxy
{-# INLINE gcd #-}

-- tg1 = reflect $ gcd nat8 nat8
-- tg2 = reflect $ gcd nat8 (pred nat8)
-- tg3 = reflect $ gcd nat8 (pred (pred nat8))
-- tg4 = reflect $ gcd (pred (pred nat8)) nat8
-- tg5 = reflect $ gcd nat4 nat8
-- tg6 = reflect $ gcd (pred nat4) (succ nat8)
-- tg7 = reflect $ gcd (succ nat8) (pred nat4)
-}

----------------------------------------------------------------
----------------------------------------------------------- fin.
