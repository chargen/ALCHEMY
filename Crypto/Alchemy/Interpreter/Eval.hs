{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE NoImplicitPrelude          #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE UndecidableInstances       #-}

module Crypto.Alchemy.Interpreter.Eval
( E, eval
)
where

import Control.Applicative
import Data.Tuple

import Algebra.Additive as Additive
import Algebra.Ring     as Ring
import NumericPrelude

import Crypto.Alchemy.Language.Arithmetic
import Crypto.Alchemy.Language.Lambda
import Crypto.Alchemy.Language.SHE

import Crypto.Lol (Cyc, RescaleCyc)
import Crypto.Lol.Applications.SymmSHE as SHE

-- | Metacircular evaluator.
newtype E e a = E { unE :: e -> a } deriving (Functor,Applicative)

-- | Evaluate a closed expression (i.e., one not having any unbound
-- variables)
eval :: E () a -> a
eval = flip unE ()

instance Lambda E where
  lam f  = E $ curry $ unE f
  ($:) = (<*>)

instance DB E a where
  v0  = E snd
  s a = E $ unE a . fst

instance (Additive.C a) => Add E a where
  x +: y = (+) <$> x <*> y

instance (Additive.C a) => AddLit E a where
  addLit x y = (x+) <$> y

instance (Ring.C a) => Mul E a where
  type PreMul E a = a
  x *: y = (*) <$> x <*> y

instance (Ring.C a) => MulLit E a where
  mulLit x y = (x*) <$> y

instance SHE E where

  type ModSwitchCtx E (CT m zp (Cyc t m' zq)) zp'     = (ModSwitchPTCtx t m' zp zp' zq)
  type RescaleCtx   E (CT m zp (Cyc t m' zq)) zq'     = (RescaleCyc (Cyc t) zq' zq, ToSDCtx t m' zp zq')
  type AddPubCtx    E (CT m zp (Cyc t m' zq))         = (AddPublicCtx t m m' zp zq)
  type MulPubCtx    E (CT m zp (Cyc t m' zq))         = (MulPublicCtx t m m' zp zq)
  type KeySwitchCtx E (CT m zp (Cyc t m' zq)) zq' gad = (SHE.KeySwitchCtx gad t m' zp zq zq')
  type TunnelCtx    E t e r s e' r' s' zp zq gad      = (SHE.TunnelCtx t r s e' r' s' zp zq gad)

  modSwitchPT     = fmap SHE.modSwitchPT
  rescaleLinearCT = fmap SHE.rescaleLinearCT
  addPublic       = fmap . SHE.addPublic
  mulPublic       = fmap . SHE.mulPublic
  keySwitchQuad   = fmap . SHE.keySwitchQuadCirc
  tunnel          = fmap . SHE.tunnelCT
