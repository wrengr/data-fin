-- TODO: see also <http://okmij.org/ftp/Haskell/PeanoArithm.lhs>
{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
{-# LANGUAGE EmptyDataDecls
           , DeriveDataTypeable
           , MultiParamTypeClasses
           , TypeFamilies
           , FlexibleContexts
           , FlexibleInstances
           , UndecidableInstances
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
--                                                    2013.08.03
-- |
-- Module      :  Data.Number.Fin.TyDecimal
-- Copyright   :  2012--2013 wren ng thornton,
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
    , SuccC, Succ, Pred, succ, pred
    -- ** addition\/subtraction
    , AddC, Add, Minus, add, minus, subtract
    -- ** comparison
    , CompareC, Compare, compare
    , NatLE, NatLT, assert_NatLE
    , MaxC, Max, max
    , MinC, Min, min
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

-- import Data.Number.Fin.TyOrdering
data LT_ deriving Typeable
data EQ_ deriving Typeable
data GT_ deriving Typeable

instance Reifies LT_ Ordering where reflect _ = LT 
instance Reifies EQ_ Ordering where reflect _ = EQ 
instance Reifies GT_ Ordering where reflect _ = GT 

-- | Compose comparison relations. Perform the first comparison,
-- and if it's not definitive, then fall through to perform the
-- second comparison.
class (NCS r1 r2 ~ r3) => NCSC r1 r2 r3 where { type NCS r1 r2 :: * }
-- class    NCS r1 r2 r3 | r1 r2 -> r3
instance NCSC EQ_ r r   where { type NCS EQ_ r = r   }
instance NCSC GT_ r GT_ where { type NCS GT_ r = GT_ }
instance NCSC LT_ r LT_ where { type NCS LT_ r = LT_ }

class (OrderingElim lt eq gt cmp ~ r) => OrderingElimC lt eq gt cmp r where
    type OrderingElim lt eq gt r1 :: *

#define __OrderingElimC(lt,eq,gt,cmp,r) \
    OrderingElimC lt eq gt cmp r where { type OrderingElim lt eq gt cmp = r }
instance __OrderingElimC(lt, eq, gt, LT_, lt)
instance __OrderingElimC(lt, eq, gt, EQ_, eq)
instance __OrderingElimC(lt, eq, gt, GT_, gt)
#undef __OrderingElimC

----------------------------------------------------------------
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
div10 = const Proxy
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
----------------------------------------------------------------
-- BUG: We can't automatically deduce (NatLE x y) nor (NatLT x y) from (Succ x y). We can add them as additional constraints on the instances; and that works to get everything in this package to typecheck, but it causes infinite loops whenever we actually try to use Succ as a type-function in real code...

-- | The successor\/predecessor relation; by structural induction
-- on the first argument. Modes:
--
-- > SuccC x (Succ x)  -- i.e., given x, return the successor of x
-- > SuccC (Pred y) y  -- i.e., given y, return the predecessor of y
--
class (Nat_ x, NatNE0_ y, Succ x ~ y, Pred y ~ x) => SuccC x y where
    type Succ x :: *
    type Pred y :: *
-- class (Nat_ x, NatNE0_ y) => SuccC x y | x -> y, y -> x

#define __SuccC(x,y) \
    SuccC x y where { type Succ x = y; type Pred y = x }
instance                __SuccC(D0,      D1)
instance                __SuccC(D1,      D2)
instance                __SuccC(D2,      D3)
instance                __SuccC(D3,      D4)
instance                __SuccC(D4,      D5)
instance                __SuccC(D5,      D6)
instance                __SuccC(D6,      D7)
instance                __SuccC(D7,      D8)
instance                __SuccC(D8,      D9)
instance                __SuccC(D9,      (D1:.D0))
instance (NatNE0_ x) => __SuccC((x:.D0), (x:.D1))
instance (NatNE0_ x) => __SuccC((x:.D1), (x:.D2))
instance (NatNE0_ x) => __SuccC((x:.D2), (x:.D3))
instance (NatNE0_ x) => __SuccC((x:.D3), (x:.D4))
instance (NatNE0_ x) => __SuccC((x:.D4), (x:.D5))
instance (NatNE0_ x) => __SuccC((x:.D5), (x:.D6))
instance (NatNE0_ x) => __SuccC((x:.D6), (x:.D7))
instance (NatNE0_ x) => __SuccC((x:.D7), (x:.D8))
instance (NatNE0_ x) => __SuccC((x:.D8), (x:.D9))
#undef __SuccC

instance (NatNE0_ x, SuccC x (y:.d)) => SuccC (x:.D9) (y :.d :.D0) where
    type Succ (x:.D9)      = (Succ x :. D0)
    type Pred (y :.d :.D0) = (Pred (y :. d) :. D9)

succ :: SuccC x y => Proxy x -> Proxy y
succ = const Proxy
{-# INLINE succ #-}

pred :: SuccC x y => Proxy y -> Proxy x
pred = const Proxy
{-# INLINE pred #-}

----------------------------------------------------------------
----------------------------------------------------------------

type family   Init y :: *
type instance Init (x :. d) = x 

type family   Last y :: *
type instance Last (x :. d) = d
    
    
-- | Assert @10*x + d == y@ where @d@ is a decimal digit and both @x@
-- and @y@ are decimal numbers. @x@ may be zero. Essentially, this
-- is the general, non-structural, constructor\/deconstructor of a
-- decimal number. This is like the assertion @x:.d ~ y@ except that
-- we trim leading zeros of @y@ in order to ensure that it is
-- well-formed.
class
    ( Digit_ d
    , Nat_ x
    , Nat_ y
    , Snoc x d ~ y
    , SInit y ~ x
    , SLast y ~ d
    ) => SnocC x d y
    where
    type Snoc x d :: *
    type SInit y :: *
    type SLast y :: *
-- class (Digit_ d, Nat_ x, Nat_ y) => SnocC x d y | x d -> y, y -> x d

#define __SnocC_D0(d) \
    SnocC D0 d d where { type Snoc D0 d = d; type SInit d = D0; type SLast d = d }
instance __SnocC_D0(D0)
instance __SnocC_D0(D1)
instance __SnocC_D0(D2)
instance __SnocC_D0(D3)
instance __SnocC_D0(D4)
instance __SnocC_D0(D5)
instance __SnocC_D0(D6)
instance __SnocC_D0(D7)
instance __SnocC_D0(D8)
instance __SnocC_D0(D9)
#undef __SnocC_D0

#define __SnocC(x,d) \
    SnocC x d (x:.d) where { type Snoc x d = x :. d; type SInit (x:.d) = x; type SLast (x:.d) = d }
instance (Digit_ d, Nat_ (D1:.d)) => __SnocC(D1,d)
instance (Digit_ d, Nat_ (D2:.d)) => __SnocC(D2,d)
instance (Digit_ d, Nat_ (D3:.d)) => __SnocC(D3,d)
instance (Digit_ d, Nat_ (D4:.d)) => __SnocC(D4,d)
instance (Digit_ d, Nat_ (D5:.d)) => __SnocC(D5,d)
instance (Digit_ d, Nat_ (D6:.d)) => __SnocC(D6,d)
instance (Digit_ d, Nat_ (D7:.d)) => __SnocC(D7,d)
instance (Digit_ d, Nat_ (D8:.d)) => __SnocC(D8,d)
instance (Digit_ d, Nat_ (D9:.d)) => __SnocC(D9,d)
#undef __SnocC
    
instance
    (Digit_ d', Nat_ (x:.d), Nat_ (x:.d:.d'))
    => SnocC (x:.d) d' (x:.d:.d')
    where
    type Snoc  (x:.d) d'  = (x:.d:.d')
    type SInit (x:.d:.d') = (x:.d)
    type SLast (x:.d:.d') = d'


----------------------------------------------------------------
-- | The primitive addition relation; by structural induction on
-- the first argument. Modes:
--
-- > AddC_ x y (Add x y)
-- > AddC_ x (Minus z x) z  -- when it's defined.
--
class
    ( Nat_ x
    , Nat_ y
    , Nat_ z
    , Add x y ~ z
    , Minus z x ~ y
    ) => AddC_ x y z
    where
    type Add x y :: *
    type Minus z x :: *
-- class (Nat_ x, Nat_ y, Nat_ z) => Add_ x y z | x y -> z, z x -> y

instance (Nat_ y) => AddC_ D0 y y where
    type Add   D0 y = y
    type Minus y D0 = y

instance (SuccC y y1) => AddC_ D1 y y1 where
    type Add   D1 y  = Succ y
    type Minus y1 D1 = Pred y1

instance (SuccC y y1, SuccC y1 y2) => AddC_ D2 y y2 where
    type Add   D2 y  = Succ (Succ y)
    type Minus y2 D2 = Pred (Pred y2)

instance (SuccC y y1, SuccC y1 y2, SuccC y2 y3) => AddC_ D3 y y3 where
    type Add   D3 y  = Succ (Succ (Succ y))
    type Minus y3 D3 = Pred (Pred (Pred y3))

instance
    ( SuccC y  y1, SuccC y1 y2, SuccC y2 y3
    , SuccC y3 y4
    ) => AddC_ D4 y y4
    where
    type Add   D4 y  = Succ (Succ (Succ (Succ y)))
    type Minus y4 D4 = Pred (Pred (Pred (Pred y4)))

instance
    ( SuccC y  y1, SuccC y1 y2, SuccC y2 y3
    , SuccC y3 y4, SuccC y4 y5
    ) => AddC_ D5 y y5
    where
    type Add   D5 y  = Succ (Succ (Succ (Succ (Succ y))))
    type Minus y5 D5 = Pred (Pred (Pred (Pred (Pred y5))))

instance
    ( SuccC y  y1, SuccC y1 y2, SuccC y2 y3
    , SuccC y3 y4, SuccC y4 y5, SuccC y5 y6
    ) => AddC_ D6 y y6
    where
    type Add   D6 y  = Succ (Succ (Succ (Succ (Succ (Succ y)))))
    type Minus y6 D6 = Pred (Pred (Pred (Pred (Pred (Pred y6)))))

instance
    ( SuccC y  y1, SuccC y1 y2, SuccC y2 y3
    , SuccC y3 y4, SuccC y4 y5, SuccC y5 y6
    , SuccC y6 y7
    ) => AddC_ D7 y y7
    where
    type Add   D7 y  = Succ (Succ (Succ (Succ (Succ (Succ (Succ y))))))
    type Minus y7 D7 = Pred (Pred (Pred (Pred (Pred (Pred (Pred y7))))))

instance
    ( SuccC y  y1, SuccC y1 y2, SuccC y2 y3
    , SuccC y3 y4, SuccC y4 y5, SuccC y5 y6
    , SuccC y6 y7, SuccC y7 y8
    ) => AddC_ D8 y y8
    where
    type Add   D8 y  = Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ y)))))))
    type Minus y8 D8 = Pred (Pred (Pred (Pred (Pred (Pred (Pred (Pred y8)))))))

instance
    ( SuccC y  y1, SuccC y1 y2, SuccC y2 y3
    , SuccC y3 y4, SuccC y4 y5, SuccC y5 y6
    , SuccC y6 y7, SuccC y7 y8, SuccC y8 y9
    ) => AddC_ D9 y y9
    where
    type Add   D9 y  = Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ y))))))))
    type Minus y9 D9 = Pred (Pred (Pred (Pred (Pred (Pred (Pred (Pred (Pred y9))))))))

instance
    (NatNE0_ x, NatNE0_ (z:.dz), AddC_ x y' z, SnocC y' dz y)
    => AddC_ (x:.D0) y (z:.dz)
    where
    type Add   (x:.D0) y       = Add x (SInit y) :. SLast y
    type Minus (z:.dz) (x:.D0) = Snoc (Minus z x) dz

#define __AddC_(x,d,y,z) \
    AddC_ (x:.d) y z where { type Add (x:.d) y = Add d (Add x (SInit y) :. SLast y); type Minus z (x:.d) = Snoc (Minus (Init (Minus z d)) x) (Last (Minus z d)) }
instance
    (NatNE0_ x, Nat_ z, AddC_ x y' zh, SnocC y' dy y, AddC_ D1 (zh:.dy) z)
    => __AddC_(x,D1,y,z)
instance
    (NatNE0_ x, Nat_ z, AddC_ x y' zh, SnocC y' dy y, AddC_ D2 (zh:.dy) z)
    => __AddC_(x,D2,y,z)
instance
    (NatNE0_ x, Nat_ z, AddC_ x y' zh, SnocC y' dy y, AddC_ D3 (zh:.dy) z)
    => __AddC_(x,D3,y,z)
instance
    (NatNE0_ x, Nat_ z, AddC_ x y' zh, SnocC y' dy y, AddC_ D4 (zh:.dy) z)
    => __AddC_(x,D4,y,z)
instance
    (NatNE0_ x, Nat_ z, AddC_ x y' zh, SnocC y' dy y, AddC_ D5 (zh:.dy) z)
    => __AddC_(x,D5,y,z)
instance
    (NatNE0_ x, Nat_ z, AddC_ x y' zh, SnocC y' dy y, AddC_ D6 (zh:.dy) z)
    => __AddC_(x,D6,y,z)
instance
    (NatNE0_ x, Nat_ z, AddC_ x y' zh, SnocC y' dy y, AddC_ D7 (zh:.dy) z)
    => __AddC_(x,D7,y,z)
instance
    (NatNE0_ x, Nat_ z, AddC_ x y' zh, SnocC y' dy y, AddC_ D8 (zh:.dy) z)
    => __AddC_(x,D8,y,z)
instance
    (NatNE0_ x, Nat_ z, AddC_ x y' zh, SnocC y' dy y, AddC_ D9 (zh:.dy) z)
    => __AddC_(x,D9,y,z)
#undef __AddC_


-- | The addition relation with full dependencies. Modes:
--
-- > AddC x y (Add x y)
-- > AddC x (Minus z x) z  -- when it's defined.
-- > AddC (Minus z y) y z  -- when it's defined.
--
class
    ( AddC_ x y z -- ==> (Add x y ~ z, Minus z x ~ y)
    , AddC_ y x z -- ==> (Add y x ~ z, Minus z y ~ x)
    ) => AddC x y z
--class (Add_ x y z, Add_ y x z) => Add x y z | x y -> z, z x -> y, z y -> x
instance (AddC_ x y z, AddC_ y x z) => AddC x y z

const2 :: a -> b -> c -> a
const2 x = (\ _ _ -> x)
{-# INLINE const2 #-}

add :: AddC x y z => Proxy x -> Proxy y -> Proxy z
add = const2 Proxy
{-# INLINE add #-}

-- | N.B., this will be ill-typed if @x@ is greater than @z@.
minus :: AddC x y z => Proxy z -> Proxy x -> Proxy y
minus = const2 Proxy
{-# INLINE minus #-}

-- | N.B., this will be ill-typed if @x@ is greater than @z@.
subtract :: AddC x y z => Proxy x -> Proxy z -> Proxy y
subtract = const2 Proxy
{-# INLINE subtract #-}

----------------------------------------------------------------
----------------------------------------------------------------
-- Equality and order: the comparison relation

-- | Assert that the comparison relation @r@ (@LT_@, @EQ_@, or
-- @GT_@) holds between @x@ and @y@; by structural induction on the
-- first, and then the second argument.
--
-- > CompareC x y (Compare x y)
--
class (Nat_ x, Nat_ y, Compare x y ~ r) => CompareC x y r where
    type Compare x y :: *
-- class (Nat_ x, Nat_ y) => CompareC x y r | x y -> r

#define __CompareC(x,y,r) \
    CompareC x y r where { type Compare x y = r }
instance                    __CompareC(D0,      D0,      EQ_)
instance                    __CompareC(D0,      D1,      LT_)
instance                    __CompareC(D0,      D2,      LT_)
instance                    __CompareC(D0,      D3,      LT_)
instance                    __CompareC(D0,      D4,      LT_)
instance                    __CompareC(D0,      D5,      LT_)
instance                    __CompareC(D0,      D6,      LT_)
instance                    __CompareC(D0,      D7,      LT_)
instance                    __CompareC(D0,      D8,      LT_)
instance                    __CompareC(D0,      D9,      LT_)
instance NatNE0_ (y:.dy) => __CompareC(D0,      (y:.dy), LT_)
instance                    __CompareC(D1,      D0,      GT_)
instance                    __CompareC(D1,      D1,      EQ_)
instance                    __CompareC(D1,      D2,      LT_)
instance                    __CompareC(D1,      D3,      LT_)
instance                    __CompareC(D1,      D4,      LT_)
instance                    __CompareC(D1,      D5,      LT_)
instance                    __CompareC(D1,      D6,      LT_)
instance                    __CompareC(D1,      D7,      LT_)
instance                    __CompareC(D1,      D8,      LT_)
instance                    __CompareC(D1,      D9,      LT_)
instance NatNE0_ (y:.dy) => __CompareC(D1,      (y:.dy), LT_)
instance                    __CompareC(D2,      D0,      GT_)
instance                    __CompareC(D2,      D1,      GT_)
instance                    __CompareC(D2,      D2,      EQ_)
instance                    __CompareC(D2,      D3,      LT_)
instance                    __CompareC(D2,      D4,      LT_)
instance                    __CompareC(D2,      D5,      LT_)
instance                    __CompareC(D2,      D6,      LT_)
instance                    __CompareC(D2,      D7,      LT_)
instance                    __CompareC(D2,      D8,      LT_)
instance                    __CompareC(D2,      D9,      LT_)
instance NatNE0_ (y:.dy) => __CompareC(D2,      (y:.dy), LT_)
instance                    __CompareC(D3,      D0,      GT_)
instance                    __CompareC(D3,      D1,      GT_)
instance                    __CompareC(D3,      D2,      GT_)
instance                    __CompareC(D3,      D3,      EQ_)
instance                    __CompareC(D3,      D4,      LT_)
instance                    __CompareC(D3,      D5,      LT_)
instance                    __CompareC(D3,      D6,      LT_)
instance                    __CompareC(D3,      D7,      LT_)
instance                    __CompareC(D3,      D8,      LT_)
instance                    __CompareC(D3,      D9,      LT_)
instance NatNE0_ (y:.dy) => __CompareC(D3,      (y:.dy), LT_)
instance                    __CompareC(D4,      D0,      GT_)
instance                    __CompareC(D4,      D1,      GT_)
instance                    __CompareC(D4,      D2,      GT_)
instance                    __CompareC(D4,      D3,      GT_)
instance                    __CompareC(D4,      D4,      EQ_)
instance                    __CompareC(D4,      D5,      LT_)
instance                    __CompareC(D4,      D6,      LT_)
instance                    __CompareC(D4,      D7,      LT_)
instance                    __CompareC(D4,      D8,      LT_)
instance                    __CompareC(D4,      D9,      LT_)
instance NatNE0_ (y:.dy) => __CompareC(D4,      (y:.dy), LT_)
instance                    __CompareC(D5,      D0,      GT_)
instance                    __CompareC(D5,      D1,      GT_)
instance                    __CompareC(D5,      D2,      GT_)
instance                    __CompareC(D5,      D3,      GT_)
instance                    __CompareC(D5,      D4,      GT_)
instance                    __CompareC(D5,      D5,      EQ_)
instance                    __CompareC(D5,      D6,      LT_)
instance                    __CompareC(D5,      D7,      LT_)
instance                    __CompareC(D5,      D8,      LT_)
instance                    __CompareC(D5,      D9,      LT_)
instance NatNE0_ (y:.dy) => __CompareC(D5,      (y:.dy), LT_)
instance                    __CompareC(D6,      D0,      GT_)
instance                    __CompareC(D6,      D1,      GT_)
instance                    __CompareC(D6,      D2,      GT_)
instance                    __CompareC(D6,      D3,      GT_)
instance                    __CompareC(D6,      D4,      GT_)
instance                    __CompareC(D6,      D5,      GT_)
instance                    __CompareC(D6,      D6,      EQ_)
instance                    __CompareC(D6,      D7,      LT_)
instance                    __CompareC(D6,      D8,      LT_)
instance                    __CompareC(D6,      D9,      LT_)
instance NatNE0_ (y:.dy) => __CompareC(D6,      (y:.dy), LT_)
instance                    __CompareC(D7,      D0,      GT_)
instance                    __CompareC(D7,      D1,      GT_)
instance                    __CompareC(D7,      D2,      GT_)
instance                    __CompareC(D7,      D3,      GT_)
instance                    __CompareC(D7,      D4,      GT_)
instance                    __CompareC(D7,      D5,      GT_)
instance                    __CompareC(D7,      D6,      GT_)
instance                    __CompareC(D7,      D7,      EQ_)
instance                    __CompareC(D7,      D8,      LT_)
instance                    __CompareC(D7,      D9,      LT_)
instance NatNE0_ (y:.dy) => __CompareC(D7,      (y:.dy), LT_)
instance                    __CompareC(D8,      D0,      GT_)
instance                    __CompareC(D8,      D1,      GT_)
instance                    __CompareC(D8,      D2,      GT_)
instance                    __CompareC(D8,      D3,      GT_)
instance                    __CompareC(D8,      D4,      GT_)
instance                    __CompareC(D8,      D5,      GT_)
instance                    __CompareC(D8,      D6,      GT_)
instance                    __CompareC(D8,      D7,      GT_)
instance                    __CompareC(D8,      D8,      EQ_)
instance                    __CompareC(D8,      D9,      LT_)
instance NatNE0_ (y:.dy) => __CompareC(D8,      (y:.dy), LT_)
instance                    __CompareC(D9,      D0,      GT_)
instance                    __CompareC(D9,      D1,      GT_)
instance                    __CompareC(D9,      D2,      GT_)
instance                    __CompareC(D9,      D3,      GT_)
instance                    __CompareC(D9,      D4,      GT_)
instance                    __CompareC(D9,      D5,      GT_)
instance                    __CompareC(D9,      D6,      GT_)
instance                    __CompareC(D9,      D7,      GT_)
instance                    __CompareC(D9,      D8,      GT_)
instance                    __CompareC(D9,      D9,      EQ_)
instance NatNE0_ (y:.dy) => __CompareC(D9,      (y:.dy), LT_)
instance NatNE0_ (x:.dx) => __CompareC((x:.dx), D0,      GT_)
instance NatNE0_ (x:.dx) => __CompareC((x:.dx), D1,      GT_)
instance NatNE0_ (x:.dx) => __CompareC((x:.dx), D2,      GT_)
instance NatNE0_ (x:.dx) => __CompareC((x:.dx), D3,      GT_)
instance NatNE0_ (x:.dx) => __CompareC((x:.dx), D4,      GT_)
instance NatNE0_ (x:.dx) => __CompareC((x:.dx), D5,      GT_)
instance NatNE0_ (x:.dx) => __CompareC((x:.dx), D6,      GT_)
instance NatNE0_ (x:.dx) => __CompareC((x:.dx), D7,      GT_)
instance NatNE0_ (x:.dx) => __CompareC((x:.dx), D8,      GT_)
instance NatNE0_ (x:.dx) => __CompareC((x:.dx), D9,      GT_)
#undef __CompareC

instance
    ( NatNE0_ (x:.dx), NatNE0_ (y:.dy)
    , CompareC dx dy dr, CompareC x y r', NCSC r' dr r
    ) => CompareC (x:.dx) (y:.dy) r where
    type Compare (x:.dx) (y:.dy) = NCS (Compare x y) (Compare dx dy)

compare :: CompareC x y r => Proxy x -> Proxy y -> Proxy r
compare = const2 Proxy
{-# INLINE compare #-}


----------------------------------------------------------------
-- BUG: is this still an optimization now that there's a combinatorial explosion?
-- | Assert that @x <= y@. This is a popular constraint, so we
-- implement it specially. We could have said that @Add n x y =>
-- NatLE x y@, but the following inductive definition is a bit
-- more optimal.
class (Nat_ x, Nat_ y) => NatLE x y
instance                                             NatLE D0 D0
instance                                             NatLE D0 D1
instance                                             NatLE D0 D2
instance                                             NatLE D0 D3
instance                                             NatLE D0 D4
instance                                             NatLE D0 D5
instance                                             NatLE D0 D6
instance                                             NatLE D0 D7
instance                                             NatLE D0 D8
instance                                             NatLE D0 D9
instance NatNE0_ (y:.dy)                          => NatLE D0 (y:.dy)
instance                                             NatLE D1 D1
instance                                             NatLE D1 D2
instance                                             NatLE D1 D3
instance                                             NatLE D1 D4
instance                                             NatLE D1 D5
instance                                             NatLE D1 D6
instance                                             NatLE D1 D7
instance                                             NatLE D1 D8
instance                                             NatLE D1 D9
instance NatNE0_ (y:.dy)                          => NatLE D1 (y:.dy)
instance                                             NatLE D2 D2
instance                                             NatLE D2 D3
instance                                             NatLE D2 D4
instance                                             NatLE D2 D5
instance                                             NatLE D2 D6
instance                                             NatLE D2 D7
instance                                             NatLE D2 D8
instance                                             NatLE D2 D9
instance NatNE0_ (y:.dy)                          => NatLE D2 (y:.dy)
instance                                             NatLE D3 D3
instance                                             NatLE D3 D4
instance                                             NatLE D3 D5
instance                                             NatLE D3 D6
instance                                             NatLE D3 D7
instance                                             NatLE D3 D8
instance                                             NatLE D3 D9
instance NatNE0_ (y:.dy)                          => NatLE D3 (y:.dy)
instance                                             NatLE D4 D4
instance                                             NatLE D4 D5
instance                                             NatLE D4 D6
instance                                             NatLE D4 D7
instance                                             NatLE D4 D8
instance                                             NatLE D4 D9
instance NatNE0_ (y:.dy)                          => NatLE D4 (y:.dy)
instance                                             NatLE D5 D5
instance                                             NatLE D5 D6
instance                                             NatLE D5 D7
instance                                             NatLE D5 D8
instance                                             NatLE D5 D9
instance NatNE0_ (y:.dy)                          => NatLE D5 (y:.dy)
instance                                             NatLE D6 D6
instance                                             NatLE D6 D7
instance                                             NatLE D6 D8
instance                                             NatLE D6 D9
instance NatNE0_ (y:.dy)                          => NatLE D6 (y:.dy)
instance                                             NatLE D7 D7
instance                                             NatLE D7 D8
instance                                             NatLE D7 D9
instance NatNE0_ (y:.dy)                          => NatLE D7 (y:.dy)
instance                                             NatLE D8 D8
instance                                             NatLE D8 D9
instance NatNE0_ (y:.dy)                          => NatLE D8 (y:.dy)
instance                                             NatLE D9 D9
instance NatNE0_ (y:.dy)                          => NatLE D9 (y:.dy)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)        => NatLE (x:.D0) (y:.D0)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)        => NatLE (x:.D0) (y:.D1)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)        => NatLE (x:.D0) (y:.D2)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)        => NatLE (x:.D0) (y:.D3)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)        => NatLE (x:.D0) (y:.D4)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)        => NatLE (x:.D0) (y:.D5)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)        => NatLE (x:.D0) (y:.D6)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)        => NatLE (x:.D0) (y:.D7)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)        => NatLE (x:.D0) (y:.D8)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)        => NatLE (x:.D0) (y:.D9)
instance (NatNE0_ x, NatNE0_ y, CompareC x y LT_) => NatLE (x:.D1) (y:.D0)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)        => NatLE (x:.D1) (y:.D1)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)        => NatLE (x:.D1) (y:.D2)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)        => NatLE (x:.D1) (y:.D3)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)        => NatLE (x:.D1) (y:.D4)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)        => NatLE (x:.D1) (y:.D5)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)        => NatLE (x:.D1) (y:.D6)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)        => NatLE (x:.D1) (y:.D7)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)        => NatLE (x:.D1) (y:.D8)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)        => NatLE (x:.D1) (y:.D9)
instance (NatNE0_ x, NatNE0_ y, CompareC x y LT_) => NatLE (x:.D2) (y:.D0)
instance (NatNE0_ x, NatNE0_ y, CompareC x y LT_) => NatLE (x:.D2) (y:.D1)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)        => NatLE (x:.D2) (y:.D2)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)        => NatLE (x:.D2) (y:.D3)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)        => NatLE (x:.D2) (y:.D4)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)        => NatLE (x:.D2) (y:.D5)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)        => NatLE (x:.D2) (y:.D6)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)        => NatLE (x:.D2) (y:.D7)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)        => NatLE (x:.D2) (y:.D8)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)        => NatLE (x:.D2) (y:.D9)
instance (NatNE0_ x, NatNE0_ y, CompareC x y LT_) => NatLE (x:.D3) (y:.D0)
instance (NatNE0_ x, NatNE0_ y, CompareC x y LT_) => NatLE (x:.D3) (y:.D1)
instance (NatNE0_ x, NatNE0_ y, CompareC x y LT_) => NatLE (x:.D3) (y:.D2)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)        => NatLE (x:.D3) (y:.D3)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)        => NatLE (x:.D3) (y:.D4)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)        => NatLE (x:.D3) (y:.D5)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)        => NatLE (x:.D3) (y:.D6)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)        => NatLE (x:.D3) (y:.D7)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)        => NatLE (x:.D3) (y:.D8)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)        => NatLE (x:.D3) (y:.D9)
instance (NatNE0_ x, NatNE0_ y, CompareC x y LT_) => NatLE (x:.D4) (y:.D0)
instance (NatNE0_ x, NatNE0_ y, CompareC x y LT_) => NatLE (x:.D4) (y:.D1)
instance (NatNE0_ x, NatNE0_ y, CompareC x y LT_) => NatLE (x:.D4) (y:.D2)
instance (NatNE0_ x, NatNE0_ y, CompareC x y LT_) => NatLE (x:.D4) (y:.D3)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)        => NatLE (x:.D4) (y:.D4)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)        => NatLE (x:.D4) (y:.D5)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)        => NatLE (x:.D4) (y:.D6)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)        => NatLE (x:.D4) (y:.D7)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)        => NatLE (x:.D4) (y:.D8)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)        => NatLE (x:.D4) (y:.D9)
instance (NatNE0_ x, NatNE0_ y, CompareC x y LT_) => NatLE (x:.D5) (y:.D0)
instance (NatNE0_ x, NatNE0_ y, CompareC x y LT_) => NatLE (x:.D5) (y:.D1)
instance (NatNE0_ x, NatNE0_ y, CompareC x y LT_) => NatLE (x:.D5) (y:.D2)
instance (NatNE0_ x, NatNE0_ y, CompareC x y LT_) => NatLE (x:.D5) (y:.D3)
instance (NatNE0_ x, NatNE0_ y, CompareC x y LT_) => NatLE (x:.D5) (y:.D4)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)        => NatLE (x:.D5) (y:.D5)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)        => NatLE (x:.D5) (y:.D6)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)        => NatLE (x:.D5) (y:.D7)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)        => NatLE (x:.D5) (y:.D8)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)        => NatLE (x:.D5) (y:.D9)
instance (NatNE0_ x, NatNE0_ y, CompareC x y LT_) => NatLE (x:.D6) (y:.D0)
instance (NatNE0_ x, NatNE0_ y, CompareC x y LT_) => NatLE (x:.D6) (y:.D1)
instance (NatNE0_ x, NatNE0_ y, CompareC x y LT_) => NatLE (x:.D6) (y:.D2)
instance (NatNE0_ x, NatNE0_ y, CompareC x y LT_) => NatLE (x:.D6) (y:.D3)
instance (NatNE0_ x, NatNE0_ y, CompareC x y LT_) => NatLE (x:.D6) (y:.D4)
instance (NatNE0_ x, NatNE0_ y, CompareC x y LT_) => NatLE (x:.D6) (y:.D5)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)        => NatLE (x:.D6) (y:.D6)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)        => NatLE (x:.D6) (y:.D7)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)        => NatLE (x:.D6) (y:.D8)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)        => NatLE (x:.D6) (y:.D9)
instance (NatNE0_ x, NatNE0_ y, CompareC x y LT_) => NatLE (x:.D7) (y:.D0)
instance (NatNE0_ x, NatNE0_ y, CompareC x y LT_) => NatLE (x:.D7) (y:.D1)
instance (NatNE0_ x, NatNE0_ y, CompareC x y LT_) => NatLE (x:.D7) (y:.D2)
instance (NatNE0_ x, NatNE0_ y, CompareC x y LT_) => NatLE (x:.D7) (y:.D3)
instance (NatNE0_ x, NatNE0_ y, CompareC x y LT_) => NatLE (x:.D7) (y:.D4)
instance (NatNE0_ x, NatNE0_ y, CompareC x y LT_) => NatLE (x:.D7) (y:.D5)
instance (NatNE0_ x, NatNE0_ y, CompareC x y LT_) => NatLE (x:.D7) (y:.D6)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)        => NatLE (x:.D7) (y:.D7)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)        => NatLE (x:.D7) (y:.D8)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)        => NatLE (x:.D7) (y:.D9)
instance (NatNE0_ x, NatNE0_ y, CompareC x y LT_) => NatLE (x:.D8) (y:.D0)
instance (NatNE0_ x, NatNE0_ y, CompareC x y LT_) => NatLE (x:.D8) (y:.D1)
instance (NatNE0_ x, NatNE0_ y, CompareC x y LT_) => NatLE (x:.D8) (y:.D2)
instance (NatNE0_ x, NatNE0_ y, CompareC x y LT_) => NatLE (x:.D8) (y:.D3)
instance (NatNE0_ x, NatNE0_ y, CompareC x y LT_) => NatLE (x:.D8) (y:.D4)
instance (NatNE0_ x, NatNE0_ y, CompareC x y LT_) => NatLE (x:.D8) (y:.D5)
instance (NatNE0_ x, NatNE0_ y, CompareC x y LT_) => NatLE (x:.D8) (y:.D6)
instance (NatNE0_ x, NatNE0_ y, CompareC x y LT_) => NatLE (x:.D8) (y:.D7)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)        => NatLE (x:.D8) (y:.D8)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)        => NatLE (x:.D8) (y:.D9)
instance (NatNE0_ x, NatNE0_ y, CompareC x y LT_) => NatLE (x:.D9) (y:.D0)
instance (NatNE0_ x, NatNE0_ y, CompareC x y LT_) => NatLE (x:.D9) (y:.D1)
instance (NatNE0_ x, NatNE0_ y, CompareC x y LT_) => NatLE (x:.D9) (y:.D2)
instance (NatNE0_ x, NatNE0_ y, CompareC x y LT_) => NatLE (x:.D9) (y:.D3)
instance (NatNE0_ x, NatNE0_ y, CompareC x y LT_) => NatLE (x:.D9) (y:.D4)
instance (NatNE0_ x, NatNE0_ y, CompareC x y LT_) => NatLE (x:.D9) (y:.D5)
instance (NatNE0_ x, NatNE0_ y, CompareC x y LT_) => NatLE (x:.D9) (y:.D6)
instance (NatNE0_ x, NatNE0_ y, CompareC x y LT_) => NatLE (x:.D9) (y:.D7)
instance (NatNE0_ x, NatNE0_ y, CompareC x y LT_) => NatLE (x:.D9) (y:.D8)
instance (NatNE0_ x, NatNE0_ y, NatLE x y)        => NatLE (x:.D9) (y:.D9)


-- | N.B., this will be ill-typed if @x@ is greater than @y@.
assert_NatLE :: NatLE x y => Proxy x -> Proxy y -> ()
assert_NatLE Proxy Proxy = ()


-- | Assert that @x < y@. This is just a shorthand for @x <= pred y@.
class         (Nat_ x, NatNE0_ y) => NatLT x y
instance (SuccC y' y, NatLE x y') => NatLT x y


-- | Choose the larger of @x@ and @y@ according to the order @r@.
--
-- > MaxC x y (Max x y)
--
class (Max x y ~ z) => MaxC x y z where
    type Max x y :: *
instance (CompareC x y r, OrderingElimC y y x r z) => MaxC x y z where
    type Max x y = OrderingElim y y x (Compare x y)
{-
class Max_ x y r z | x y r -> z
instance Max_ x y LT_ y
instance Max_ x y EQ_ y -- doesn't matter which we pick
instance Max_ x y GT_ x
-}


-- | Choose the larger of @x@ and @y@.
max :: (MaxC x y z) => Proxy x -> Proxy y -> Proxy z
-- max :: (CompareC x y r, Max_ x y r z) => Proxy x -> Proxy y -> Proxy z
max = const2 Proxy
{-# INLINE max #-}


-- | Choose the smaller of @x@ and @y@ according to the order @r@.
--
-- > MinC x y (Min x y)
--
class (Min x y ~ z) => MinC x y z where
    type Min x y :: *
instance (CompareC x y r, OrderingElimC x x y r z) => MinC x y z where
    type Min x y = OrderingElim x x y (Compare x y)
{-
class    Min_ x y r   z | x y r -> z
instance Min_ x y LT_ x
instance Min_ x y EQ_ x -- doesn't matter which we pick
instance Min_ x y GT_ y
-}

-- | Choose the smaller of @x@ and @y@.
min :: (MinC x y z) => Proxy x -> Proxy y -> Proxy z
-- min :: (CompareC x y r, Min_ x y r z) => Proxy x -> Proxy y -> Proxy z
min = const2 Proxy
{-# INLINE min #-}


{-
----------------------------------------------------------------
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
mul = const2 Proxy
{-# INLINE mul #-}

-- | N.B., this will be ill-typed if @z@ is not a multiple of @x@.
div :: Mul x y z => Proxy z -> Proxy x -> Proxy y
div = const2 Proxy
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
exp2 = const Proxy
{-# INLINE exp2 #-}

-- | N.B., this will be ill-typed if @y@ is not a power of 2.
log2 :: Exp2 x y => Proxy y -> Proxy x
log2 = const Proxy
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
instance (CompareC (x:.dx) y r, GCD_ r (x:.dx) y z) => GCD (x:.dx) y z

class (NatNE0_ x, Nat_ y, Nat_ z) => GCD_ r x y z | r x y -> z
instance NatNE0_ x                           => GCD_ EQ_ x x x
instance (GCD y x z, NatNE0_ x)              => GCD_ GT_ x y z
instance (Add x y1 y, GCD y1 x z, NatNE0_ x) => GCD_ LT_ x y z

gcd :: GCD x y z => Proxy x -> Proxy y -> Proxy z
gcd = const2 Proxy
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
