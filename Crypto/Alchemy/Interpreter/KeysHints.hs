{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE NoImplicitPrelude          #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeFamilies               #-}

-- | Functions for looking up/generating keys and key-switch hints.
module Crypto.Alchemy.Interpreter.KeysHints
( Keys, Hints, KeysHints, KeysNoiseCtx, lookupKey -- not lookupHint, which is too general
, getKey, getQuadCircHint, getTunnelHint
, runKeysHints, evalKeysHints
)
where

import Control.Monad.Random
import Control.Monad.Reader
import Control.Monad.State

import Algebra.Algebraic
import Data.Dynamic
import Data.Functor
import Data.Maybe   (mapMaybe)
import Data.Monoid

import Crypto.Alchemy.MonadAccumulator
import Crypto.Lol                      hiding (lift)
import Crypto.Lol.Applications.SymmSHE


---- Monad helper functions

-- | Wrapper for a dynamic list of keys.
newtype Keys = Keys { unKeys :: [Dynamic] } deriving (Monoid, Show)

-- | Wrapper for a dynamic list of hints.
newtype Hints = Hints { unHints :: [Dynamic] } deriving (Monoid, Show)

-- | Type synonym for a standard Keys/Hints accumulator
type KeysHints v m a = StateT Keys (StateT Hints (ReaderT v m)) a

type KeysNoiseCtx v mon = (Algebraic v, MonadReader v mon, MonadRandom mon, MonadAccumulator Keys mon)

-- | Convenience function.
runKeysHints :: (Functor m) => v -> KeysHints v m a -> m (a, Keys, Hints)
runKeysHints v = ((\((a,b),c) -> (a,b,c)) <$>) .
  flip runReaderT v . runAccumulatorT . runAccumulatorT

-- | Output the output of the computation, discarding the accumulated result.
evalKeysHints :: (Functor m) => v -> KeysHints v m a -> m a
evalKeysHints v = ((\(a,_,_) -> a) <$>) . runKeysHints v

lookupDyn :: (Typeable a) => [Dynamic] -> Maybe a
lookupDyn ds = case mapMaybe fromDynamic ds of
                 []    -> Nothing
                 (x:_) -> Just x

-- | Look up a key of the desired type, if it exists.
lookupKey :: (MonadReader Keys m, Typeable (SK (Cyc t m' z)))
             => m (Maybe (SK (Cyc t m' z)))
lookupKey = (lookupDyn . unKeys) <$> ask

-- | Look up a hint of the desired type, if it exists.  (This works
-- for both QuadCircHints and TunnelHints; the function is not
-- specialized to enforce a particular one of these.)
lookupHint :: (MonadReader Hints m, Typeable a) => m (Maybe a)
lookupHint = (lookupDyn . unHints) <$> ask

-- | Append a key to the internal state.
appendKey :: (MonadAccumulator Keys m, Typeable (Cyc t m' z))
  => SK (Cyc t m' z) -> m ()
appendKey a = append $ Keys [toDyn a]

-- | Append a hint to the internal state.
appendHint :: (MonadAccumulator Hints m, Typeable a) => a -> m ()
appendHint a = append $ Hints [toDyn a]

-- | Perform the action, then perform the action given by the result,
-- and return the (first) result.
(>=<) :: (Monad m) => (a -> m ()) -> m a -> m a
f >=< a = do
  a' <- a
  f a'
  return a'

-- | Return \( r / \varphi(m') \).
svar :: (Fact m', Algebraic v) => Proxy m' -> v -> v
svar pm' r = r / (sqrt $ fromIntegral $ proxy totientFact pm')

-- | Lookup a key, generating one if it doesn't exist, and return it.
getKey :: forall z t m' mon v. -- z first for type applications
  (Algebraic v, MonadReader v mon, MonadAccumulator Keys mon,
   MonadRandom mon, GenSKCtx t m' z v, Typeable (Cyc t m' z))
  => mon (SK (Cyc t m' z))
getKey = readerToAccumulator lookupKey >>= \case
  (Just t) -> return t
  -- generate and save a key, using the adjusted variance from the monad
  Nothing -> appendKey >=< (genSK =<< svar (Proxy::Proxy m') <$> ask)

-- | Lookup a (quadratic, circular) key-switch hint, generating one
-- (and the underlying key if necessary) if it doesn't exist, and
-- return it.
getQuadCircHint :: forall v mon t z gad m' zq' .
  (-- constraints for getKey
   KeysNoiseCtx v mon, MonadAccumulator Hints mon, GenSKCtx t m' z v, Typeable (Cyc t m' z),
   -- constraints for lookup
   Typeable (KSQuadCircHint gad (Cyc t m' zq')),
   -- constraints for ksQuadCircHint
   KSHintCtx gad t m' z zq')
  => Proxy z -> mon (KSQuadCircHint gad (Cyc t m' zq'))
getQuadCircHint _ = readerToAccumulator lookupHint >>= \case
  (Just h) -> return h
  Nothing -> do
    sk :: SK (Cyc t m' z) <- getKey
    appendHint >=< ksQuadCircHint sk

-- not memoized right now, but could be if we also store the linear
-- function as part of the lookup key

-- EAC: https://ghc.haskell.org/trac/ghc/ticket/13490
-- | Generate a hint for tunneling. The result is /not/ memoized.
getTunnelHint :: forall gad zq mon t e r s e' r' s' z zp v.
  (KeysNoiseCtx v mon, GenSKCtx t r' z v, Typeable (Cyc t r' z),
   GenSKCtx t s' z v, Typeable (Cyc t s' z),
   TunnelHintCtx t e r s e' r' s' z zp zq gad)
  => Proxy z -> Linear t zp e r s
  -> mon (TunnelHint gad t e r s e' r' s' zp zq)
getTunnelHint _ linf = do
  skout <- getKey @z
  skin <- getKey @z
  tunnelHint linf skout skin
