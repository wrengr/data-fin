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
----------------------------------------------------------------
--                                                    2013.01.06
-- |
-- Module      :  Data.Number.Fin.TyBinary
-- Copyright   :  2012--2013 wren ng thornton,
--                2004--2007 Oleg Kiselyov and Chung-chieh Shan
-- License     :  BSD3
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Type-level binary natural numbers. This is based on [1], and is
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
module Data.Number.Fin.TyBinary
    (
    -- * Representation
    -- ** Type-level binary natural numbers
      B0, B1, (:.)
    -- ** Type-level 'Ordering'
    , LT_, EQ_, GT_
    
    -- * Kind predicates
    , Nat, NatNE0
    -- * sample @Nat@ types and proxies for their values
    , Nat0, Nat1, Nat2, Nat3, Nat4, Nat5, Nat6, Nat7, Nat8, Nat9
    , nat0, nat1, nat2, nat3, nat4, nat5, nat6, nat7, nat8, nat9
    
    -- * Arithmetic
    -- ** successor\/predecessor
    , Succ, succ, pred
    -- ** addition\/subtraction
    , Add, add, minus, subtract
    -- ** comparison
    , Compare, compare, NatLE, NatLT, assert_leq, min, max
    -- ** multiplication\/division
    , Mul, mul, div, div2 -- mul2 ?
    -- ** exponentiation\/logarithm
    , Exp2, exp2, log2
    -- ** GCD
    , GCD, gcd
    ) where

import Prelude hiding  (succ, pred, subtract, compare, div, gcd, max, min)
import Data.Typeable   (Typeable)
import Data.Proxy      (Proxy(Proxy))
import Data.Reflection (Reifies(reflect))
----------------------------------------------------------------

{-
Representation of binary numbers and arithmetic relations

    Representation
    B0         - 0
    B1         - 1
    B1:.B0     - 2
    B1:.B1     - 3
    B1:.B0:.B0 - 4
    B1:.B0:.B1 - 5
    B1:.B1:.B0 - 6
    B1:.B0:.B1:.B0 - 10

If we disregard the parenthesis, we see the sequence of U followed
by the number in the conventional binary notation. The number of
leading Us is the binary logarithm (if we assume log2 0 = 0), or
the number of digits in the number minus 1.
-}

-- | The zero bit.
data B0 deriving Typeable

-- | The one bit.
data B1 deriving Typeable

-- | The connective. This should only be used left associatively
-- (it associates to the left naturally). Binary digits are
-- lexicographically big-endian, so they're written as usual;
-- however, they're structurally little-endian due to the left
-- associativity.
--
-- > 0 -->         B0
-- > 1 -->         B1
-- > 2 -->     B1:.B0
-- > 3 -->     B1:.B1
-- > 4 --> B1:.B0:.B0
-- > 5 --> B1:.B0:.B1
-- > 6 --> B1:.B1:.B0
-- > 7 --> B1:.B1:.B1
--
data x :. y deriving Typeable
infixl 5 :.


-- | Is @n@ a well-formed type of kind @Nat@? The only well-formed
-- types of kind @Nat@ are type-level natural numbers in structurally
-- little-endian binary.
--
-- The hidden type class @Nat_ n@ entails @Reifies n Integer@.
class    Nat_ n => Nat n
instance Nat_ n => Nat n -- this instance is "undecidable"


-- | Is @n@ a well-formed type of kind @NatNE0@? The only well-formed
-- types of kind @NatNE0@ are the non-zero well-formed types of
-- kind @Nat@;, i.e., the type-level whole numbers in structurally
-- little-endian binary.
--
-- The hidden type class @NatNE0_ n@ entails @Nat_ n@ and @Reifies n Integer@.
class    NatNE0_ n => NatNE0 n
instance NatNE0_ n => NatNE0 n -- this instance is "undecidable"


-- for internal use only.
class    Digit_ d
instance Digit_ B0
instance Digit_ B1

-- for internal use only.
class (Reifies n Integer, Nat_ n) => NatNE0_ n
instance              NatNE0_ B1
instance NatNE0_ n => NatNE0_ (n:.B0)
instance NatNE0_ n => NatNE0_ (n:.B1)

-- for internal use only.
class Reifies n Integer => Nat_ n
instance Nat_ B0
instance Nat_ B1
instance NatNE0_ x => Nat_ (x:.B0)
instance NatNE0_ x => Nat_ (x:.B1)

instance Reifies B0 Integer where
    reflect _ = 0
instance Reifies B1 Integer where
    reflect _ = 1
instance NatNE0_ x => Reifies (x:.B0) Integer where
    reflect p = 2 * reflect (div2 p)
instance NatNE0_ x => Reifies (x:.B1) Integer where
    reflect p = 2 * reflect (div2 p) + 1

{-
-- BEWARE: Context reduction stack overflow; size = 20
type MaxBoundInt8  = B1:.B1:.B1:.B1:.B1:.B1:.B1
type MaxBoundInt16 = MaxBoundInt8:.B1:.B1:.B1:.B1:.B1:.B1:.B1:.B1
type MaxBoundInt32 = Positive (D2 (D1(D4(D7 (D4(D8(D3 (D6(D4(D7 D_))))))))))
type MaxBoundInt64 =
    Positive (D9 (D2(D2(D3 (D3(D7(D2 (D0(D3(D6 (D8(D5(D4 (D7(D7(D5 (D8(D0(D7
    D_)))))))))))))))))))
-- TODO: MaxBoundInt
type MaxBoundWord8  = B1:.B1:.B1:.B1:.B1:.B1:.B1:.B1
type MaxBoundWord16 = MaxBoundWord8:.B1:.B1:.B1:.B1:.B1:.B1:.B1:.B1
type MaxBoundWord32 = Positive (D4 (D2(D9(D4 (D9(D6(D7 (D2(D9(D5 D_))))))))))
type MaxBoundWord64 =
    Positive (D1(D8 (D4(D4(D6 (D7(D4(D4 (D0(D7(D3 (D7(D0(D9 (D5(D5(D1 (D6(D1(D5
    D_))))))))))))))))))))
    
instance Reifies B0 Int8 where reflect_ _ = inhabit 0
instance Reifies B1 Int8 where reflect_ _ = inhabit 1
instance (NatNE0_ x, NatLE (x:.B0) MaxBoundInt8)
    => Reifies (x:.B0) Int8
    where reflect_ p = inhabit $! 2 * (choose . reflect . div2) p
instance (NatNE0_ x, NatLE (x:.B1) MaxBoundInt8)
    => Reifies (x:.B1) Int8
    where reflect_ p = inhabit $! 2 * (choose . reflect . div2) p + 1

instance Reifies B0 Int16 where reflect_ _ = inhabit 0
instance Reifies B1 Int16 where reflect_ _ = inhabit 1
instance (NatNE0_ x, NatLE (x:.B0) MaxBoundInt16)
    => Reifies (x:.B0) Int16
    where reflect_ p = inhabit $! 2 * (choose . reflect . div2) p
instance (NatNE0_ x, NatLE (x:.B1) MaxBoundInt16)
    => Reifies (x:.B1) Int16
    where reflect_ p = inhabit $! 2 * (choose . reflect . div2) p + 1

instance Reifies B0 Int32 where reflect_ _ = inhabit 0
instance Reifies B1 Int32 where reflect_ _ = inhabit 1
instance (NatNE0_ x, NatLE (x:.B0) MaxBoundInt32)
    => Reifies (x:.B0) Int32
    where reflect_ p = inhabit $! 2 * (choose . reflect . div2) p
instance (NatNE0_ x, NatLE (x:.B1) MaxBoundInt32)
    => Reifies (x:.B1) Int32
    where reflect_ p = inhabit $! 2 * (choose . reflect . div2) p + 1

instance Reifies B0 Int64 where reflect_ _ = inhabit 0
instance Reifies B1 Int64 where reflect_ _ = inhabit 1
instance (NatNE0_ x, NatLE (x:.B0) MaxBoundInt64)
    => Reifies (x:.B0) Int64
    where reflect_ p = inhabit $! 2 * (choose . reflect . div2) p
instance (NatNE0_ x, NatLE (x:.B1) MaxBoundInt64)
    => Reifies (x:.B1) Int64
    where reflect_ p = inhabit $! 2 * (choose . reflect . div2) p + 1

instance Reifies B0 Int where reflect_ _ = inhabit 0
instance Reifies B1 Int where reflect_ _ = inhabit 1
instance (NatNE0_ x, NatLE (x:.B0) MaxBoundInt)
    => Reifies (x:.B0) Int
    where reflect_ p = inhabit $! 2 * (choose . reflect . div2) p
instance (NatNE0_ x, NatLE (x:.B1) MaxBoundInt)
    => Reifies (x:.B1) Int
    where reflect_ p = inhabit $! 2 * (choose . reflect . div2) p + 1
-}

-- HACK: we can't actually monomorphize the input, given our use case.
-- | Return a 'Proxy' for the floor of the input divided by 2. Using
-- @div2 n@ differs from using @n \`div\` nat2@ in that we take the
-- floor of the result rather than being ill-typed; also in that
-- @div2@ isn't defined on @B0@ or @B1@.
div2 :: proxy (h:.t) -> Proxy h
div2 _ = Proxy
{-# INLINE div2 #-}

-- some popular numbers
type Nat0 = B0 
type Nat1 = B1 
type Nat2 = B1:.B0 
type Nat3 = B1:.B1 
type Nat4 = B1:.B0:.B0 
type Nat5 = B1:.B0:.B1 
type Nat6 = B1:.B1:.B0 
type Nat7 = B1:.B1:.B1 
type Nat8 = B1:.B0:.B0:.B0 
type Nat9 = B1:.B0:.B0:.B1 

nat0 :: Proxy Nat0; nat0 = Proxy 
nat1 :: Proxy Nat1; nat1 = Proxy 
nat2 :: Proxy Nat2; nat2 = Proxy 
nat3 :: Proxy Nat3; nat3 = Proxy 
nat4 :: Proxy Nat4; nat4 = Proxy 
nat5 :: Proxy Nat5; nat5 = Proxy 
nat6 :: Proxy Nat6; nat6 = Proxy 
nat7 :: Proxy Nat7; nat7 = Proxy 
nat8 :: Proxy Nat8; nat8 = Proxy 
nat9 :: Proxy Nat9; nat9 = Proxy 

-- tn8 = reflect nat8


----------------------------------------------------------------
-- | The successor\/predecessor relation; by structural induction
-- on the first argument. Modes:
--
-- > Succ x (succ x)
-- > Succ (pred y) y
--
class (Nat_ x, NatNE0_ y) => Succ x y | x -> y, y -> x
instance                               Succ B0      B1
instance                               Succ B1      (B1:.B0)
instance (NatNE0_ x)                => Succ (x:.B0) (x :.B1)
instance (NatNE0_ x, Succ x (y:.d)) => Succ (x:.B1) (y :.d :.B0)
-- this last case triggers the need for undecidable instances <sigh>

succ :: Succ x y => Proxy x -> Proxy y
succ _ = Proxy
{-# INLINE succ #-}

pred :: Succ x y => Proxy y -> Proxy x
pred _ = Proxy
{-# INLINE pred #-}

-- tn9 = reflect $ succ nat8
-- tn7 = reflect $ pred nat8


-- | Assert @2*x + d == y@ where @d@ is a binary digit and both @x@
-- and @y@ are binary numbers. @x@ may be zero. Essentially, this
-- is the general, non-structural, constructor\/deconstructor of a
-- binary number. This is like the assertion @x:.d ~ y@ except that
-- we trim leading zeros of @y@ in order to ensure that it is
-- well-formed.
class (Digit_ d, Nat_ x, Nat_ y) => Snoc x d y | x d -> y, y -> x d
instance                                              Snoc B0     B0 B0
instance                                              Snoc B0     B1 B1
instance (Digit_ d,  Nat_ (B1:.d))                 => Snoc B1     d  (B1:.d)
instance (Digit_ d', Nat_ (x:.d), Nat_ (x:.d:.d')) => Snoc (x:.d) d' (x:.d:.d')


-- | The primitive addition relation; by structural induction on
-- the first argument. Modes:
--
-- > Add_ x y (x+y)
-- > Add_ x (z-x) z -- when it's defined.
--
class (Nat_ x, Nat_ y, Nat_ z) => Add_ x y z | x y -> z, z x -> y
instance Nat_ y   => Add_ B0 y y
instance Succ y z => Add_ B1 y z
instance (NatNE0_ x, NatNE0_ (z:.dz), Add_ x y' z, Snoc y' dz y)
    => Add_ (x:.B0) y (z:.dz)
instance (NatNE0_ x, Nat_ z, Add_ x y' zh, Snoc y' dy y, Succ (zh:.dy) z)
    => Add_ (x:.B1) y z


-- | The addition relation with full dependencies. Modes:
--
-- > Add x y (x+y)
-- > Add x (z-x) z -- when it's defined.
-- > Add (z-y) y z -- when it's defined.
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

-- ts16  = add nat8 nat8
-- ts16' = add (succ nat8) (pred nat8)
-- ts14  = add (pred nat8) (pred nat8)
-- ts0   = minus nat8 nat8
-- ts4   = reflect $ minus nat8 nat4
-- ts4'  = minus nat4 nat8 -- expected error


----------------------------------------------------------------
-- Equality and order: the comparison relation
data LT_
data EQ_
data GT_

instance Reifies LT_ Ordering where reflect _ = LT 
instance Reifies EQ_ Ordering where reflect _ = EQ 
instance Reifies GT_ Ordering where reflect _ = GT 


-- | Compose comparison relations. Perform the first comparison,
-- and if it's not definitive, then fall through to perform the
-- second comparison.
class    NCS r1 r2 r3 | r1 r2 -> r3
instance NCS EQ_ r r
instance NCS GT_ r GT_
instance NCS LT_ r LT_


-- | Assert that the comparison relation @r@ (@LT_@, @EQ_@, or
-- @GT_@) holds between @x@ and @y@; by structural induction on the
-- first, and then the second argument.
class   (Nat_ x, Nat_ y) => Compare x y r | x y -> r
instance                    Compare B0 B0      EQ_
instance                    Compare B0 B1      LT_
instance NatNE0_ (y:.dy) => Compare B0 (y:.dy) LT_
instance                    Compare B1 B0      GT_
instance                    Compare B1 B1      EQ_
instance NatNE0_ (y:.dy) => Compare B1 (y:.dy) LT_
instance NatNE0_ (x:.dx) => Compare (x:.dx) B0 GT_
instance NatNE0_ (x:.dx) => Compare (x:.dx) B1 GT_
instance
    ( NatNE0_ (x:.dx), NatNE0_ (y:.dy)
    , Compare dx dy dr, Compare x y r', NCS r' dr r
    ) => Compare (x:.dx) (y:.dy) r

compare :: Compare x y r => Proxy x -> Proxy y -> Proxy r
compare _ _ = Proxy
{-# INLINE compare #-}

-- tc1 = compare nat0 nat0
-- tc2 = compare nat8 nat8
-- tc3 = compare (succ nat8) nat8
-- tc4 = compare nat8 (succ nat8)
-- tc5 = compare (pred nat8) nat8
-- tc6 = compare nat8 (pred nat8)


-- | Assert that @x <= y@. This is a popular constraint, so we
-- implement it specially. We could have said that @Add n x y =>
-- NatLE x y@, but the following inductive definition is a bit
-- more optimal.
class (Nat_ x, Nat_ y) => NatLE x y
instance                                            NatLE B0 B0
instance                                            NatLE B0 B1
instance NatNE0_ (y:.dy)                         => NatLE B0 (y:.dy)
instance                                            NatLE B1 B1
instance NatNE0_ (y:.dy)                         => NatLE B1 (y:.dy)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)       => NatLE (x:.B0) (y:.B0)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)       => NatLE (x:.B1) (y:.B1)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)       => NatLE (x:.B0) (y:.B1)
instance (NatNE0_ x, NatNE0_ y, Compare x y LT_) => NatLE (x:.B1) (y:.B0)

-- | N.B., this will be ill-typed if @x@ is greater than @y@.
assert_leq :: NatLE x y => Proxy x -> Proxy y -> ()
assert_leq Proxy Proxy = ()

-- tle1  = assert_leq nat0 nat0
-- tle2  = assert_leq nat8 nat8
-- tle3  = assert_leq nat4 nat8
-- tle31 = assert_leq nat8 nat4 -- expected error
-- tle4  = assert_leq nat8 (succ nat8)
-- tle5  = assert_leq (pred nat8) (succ nat8)
-- tle6  = assert_leq (pred nat8) nat8
-- tle61 = assert_leq nat8 (pred nat8) -- expected error

-- | Assert that @x < y@. This is just a shorthand for @x <= pred y@.
class        (Nat_ x, NatNE0_ y) => NatLT x y
instance (Succ y' y, NatLE x y') => NatLT x y


-- | Choose the larger of @x@ and @y@ according to the order @r@.
class Max_ x y r z | x y r -> z
instance Max_ x y LT_ y
instance Max_ x y EQ_ y -- doesn't matter which we pick
instance Max_ x y GT_ x

-- | Choose the larger of @x@ and @y@.
max :: (Compare x y r, Max_ x y r z) => Proxy x -> Proxy y -> Proxy z
max _ _ = Proxy
{-# INLINE max #-}

-- tmx1 = max nat4 nat8
-- tmx2 = max nat8 nat4
-- tmx3 = max nat8 nat8

-- | Choose the smaller of @x@ and @y@ according to the order @r@.
class Min_ x y r z | x y r -> z
instance Min_ x y LT_ x
instance Min_ x y EQ_ x -- doesn't matter which we pick
instance Min_ x y GT_ y

-- | Choose the smaller of @x@ and @y@.
min :: (Compare x y r, Min_ x y r z) => Proxy x -> Proxy y -> Proxy z
min _ _ = Proxy
{-# INLINE min #-}

-- tmn1 = min nat4 nat8
-- tmn2 = min nat8 nat4
-- tmn3 = min nat8 nat8


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

----------------------------------------------------------------
----------------------------------------------------------- fin.
