data-fin
========
[![Hackage version](https://img.shields.io/hackage/v/data-fin.svg?style=flat)](https://hackage.haskell.org/package/data-fin) 
[![Build Status](https://github.com/wrengr/data-fin/workflows/ci/badge.svg)](https://github.com/wrengr/data-fin/actions?query=workflow%3Aci)
[![Dependencies](https://img.shields.io/hackage-deps/v/data-fin.svg?style=flat)](http://packdeps.haskellers.com/specific?package=data-fin)

This package provides the family of canonical finite sets, indexed
by natural numbers giving their cardinality. In addition, we provide
an implementation of type-level decimal numbers and arithmetic on
them.


## Install

While this package uses complex type machinery, it should be easy
to install. You should be able install it via the standard:

    $> cabal install data-fin
    

## Portability

While I usually try to keep things as portable as possible, this
package relies on many GHC language extensions. Thus, no claim of
portability ot non-GHC compilers is made. All the required language
extensions are:

* CPP
* DeriveDataTypeable
* EmptyDataDecls
* FlexibleContexts
* FlexibleInstances
* FunctionalDependencies
* MultiParamTypeClasses
* Rank2Types
* ScopedTypeVariables
* TypeOperators
* Trustworthy - GHC >= 7.1 only
* UndecidableInstances

## Links

* [Website](http://wrengr.org/)
* [Blog](http://winterkoninkje.dreamwidth.org/)
* [Twitter](https://twitter.com/wrengr)
* [Hackage](http://hackage.haskell.org/package/data-fin)
* [GitHub](https://github.com/wrengr/data-fin)
