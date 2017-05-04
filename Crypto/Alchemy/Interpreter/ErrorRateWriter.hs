{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE NoImplicitPrelude          #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE UndecidableInstances       #-}

module Crypto.Alchemy.Interpreter.ErrorRateWriter
( ErrorRateWriter, writeErrorRates, Monadify, ErrorRateLog )
where

import Control.Applicative
import Control.Monad.Reader
import Control.Monad.Writer

import Crypto.Lol
import Crypto.Lol.Applications.SymmSHE

import Crypto.Alchemy.Interpreter.KeysHints
import Crypto.Alchemy.Language.Arithmetic
import Crypto.Alchemy.Language.Lambda
import Crypto.Alchemy.Language.Monad
import Crypto.Alchemy.Language.SHE

-- | A transformer that additionally logs the sizes of the noise terms
-- of any ciphertexts created during interpretation.
newtype ErrorRateWriter
  expr                          -- | the underyling interpreter
  k                             -- | (reader) monad that supplies the
                                -- keys for extracting error
  w                             -- | (writer) monad for logging error rates
  e                             -- | environment
  a                             -- | represented type
  = ERW { unERW :: k (expr (Monadify w e) (Monadify w a)) }
    deriving (Functor)

type family Monadify m a where
  Monadify m (a,b) = (Monadify m a, Monadify m b)
  Monadify m (a -> b) = Monadify m a -> Monadify m b
  Monadify m a = m a

-- CJP: could generalize to (String, Double) to allow messages, but
-- then we need pairs in the object language!  (We already need lists
-- though...)
type ErrorRateLog = [Double]

-- | Transform an expression into (a monadic) one that logs error
-- rates, where the needed keys are obtained from the monad.
writeErrorRates :: ErrorRateWriter expr k w e a
                -> k (expr (Monadify w e) (Monadify w a))
writeErrorRates = unERW

instance (Lambda expr, Applicative k)
  => Lambda (ErrorRateWriter expr k w) where

  lam (ERW f) = ERW $ lam <$> f
  (ERW f) $: (ERW a) = ERW $ ($:) <$> f <*> a

  v0     = ERW $ pure v0
  s (ERW a) = ERW $ s <$> a


instance (MonadWriter ErrorRateLog w, MonadReader Keys k,
          ct ~ (CT m zp (Cyc t m zq)),
          ErrorRate expr, Applicative_ expr, Add expr ct)
         => Add (ErrorRateWriter expr k w) ct where

  add_ = ERW $ pure $ liftA2_ $: add_

  -- don't log error because it doesn't grow
  neg_ = ERW $ pure $ liftA_ $: neg_

instance (MonadWriter ErrorRateLog w, MonadReader Keys k,
          ct ~ (CT m zp (Cyc t m zq)),
          -- needed because PreMul could take some crazy form
          Monadify w (PreMul expr ct) ~ w (PreMul expr ct),
          ErrorRate expr, Applicative_ expr, Mul expr ct)
         => Mul (ErrorRateWriter expr k w) ct where

  type PreMul (ErrorRateWriter expr k w) ct = PreMul expr ct

  mul_ = ERW $ pure $ liftA2_ $: mul_
