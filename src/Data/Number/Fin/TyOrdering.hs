{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
{-# LANGUAGE EmptyDataDecls
           , DeriveDataTypeable
           , MultiParamTypeClasses
           , FlexibleInstances
           , FunctionalDependencies
           #-}

{-# LANGUAGE CPP #-}
#if __GLASGOW_HASKELL__ >= 701
{-# LANGUAGE Safe #-}
#endif
----------------------------------------------------------------
--                                                    2013.05.29
-- |
-- Module      :  Data.Number.Fin.TyOrdering
-- Copyright   :  2012--2013 wren gayle romano,
--                2004--2007 Oleg Kiselyov and Chung-chieh Shan
-- License     :  BSD3
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Type-level 'Ordering'. This is based on [1], and is intended to
-- work with [2] (though we use the @reflection@ package for the
-- actual reification part).
--
-- A lot of this also duplicates the functionality in
-- @HList:Data.HList.FakePrelude@[3], which is (or should be)
-- obviated by the new data kinds extension. However, we don't want
-- to restrict this module to the newer versions of GHC which support
-- data kinds.
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
module Data.Number.Fin.TyOrdering
    (
    -- * Type-level 'Ordering'
      LT_, EQ_, GT_
    -- * The 'NCS' class
    , NCS()
    ) where

import Data.Typeable   (Typeable)
import Data.Reflection (Reifies(reflect))
----------------------------------------------------------------

-- Equality and order: the comparison relation
data LT_ deriving Typeable
data EQ_ deriving Typeable
data GT_ deriving Typeable

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

----------------------------------------------------------------
----------------------------------------------------------- fin.
