data-fin
========
[![Hackage version](https://img.shields.io/hackage/v/data-fin.svg?style=flat)](https://hackage.haskell.org/package/data-fin) 
[![Hackage-Deps](https://img.shields.io/hackage-deps/v/data-fin.svg?style=flat)](http://packdeps.haskellers.com/specific?package=data-fin)
[![TravisCI Build Status](https://img.shields.io/travis/wrengr/data-fin.svg?style=flat)](https://travis-ci.org/wrengr/data-fin) 
[![CircleCI Build Status](https://circleci.com/gh/wrengr/data-fin.svg?style=shield&circle-token=b57517657c556be6fd8fca92b843f9e4cffaf8d1)](https://circleci.com/gh/wrengr/data-fin)

This package provides the family of canonical finite sets, indexed
by natural numbers giving their cardinality. In addition, we provide
an implementation of type-level decimal numbers and arithmetic on
them.


## Install

While this package uses complex type machinery, it should be easy
to install. You should be able to use one of the following standard
methods to install it.

    -- With cabal-install and without the source:
    $> cabal install data-fin
    
    -- With cabal-install and with the source already:
    $> cd data-fin
    $> cabal install
    
    -- Without cabal-install, but with the source already:
    $> cd data-fin
    $> runhaskell Setup.hs configure --user
    $> runhaskell Setup.hs build
    $> runhaskell Setup.hs test
    $> runhaskell Setup.hs haddock --hyperlink-source
    $> runhaskell Setup.hs copy
    $> runhaskell Setup.hs register

The test step is optional and currently does nothing. The Haddock
step is also optional.


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

* [Website](http://cl.indiana.edu/~wren/)
* [Blog](http://winterkoninkje.dreamwidth.org/)
* [Twitter](https://twitter.com/wrengr)
* [Hackage](http://hackage.haskell.org/package/data-fin)
* [Darcs](http://code.haskell.org/~wren/data-fin)
* [GitHub (clone)](https://github.com/wrengr/data-fin)
* [Haddock (Darcs version)
    ](http://code.haskell.org/~wren/data-fin/dist/doc/html/data-fin)
