{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE InstanceSigs               #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE UndecidableInstances       #-}

{-# OPTIONS_GHC -fno-warn-unused-binds  #-}

-- should be a hidden/internal module
module Crypto.Alchemy.Interpreter.PT2CT.Noise
( PNoise(..), (:+), Units(..)
, NatToLit, natType, natDec
, pNoiseUnit, PNoiseTag(..)
, UnitsToModulus, TotalUnits) where

import Algebra.Additive    as Additive (C)
import Algebra.Ring        as Ring (C)
import Data.Type.Natural   hiding ((:+))
import GHC.TypeLits        hiding (Nat)
import Language.Haskell.TH

-- | "Bits" per noise unit.
pNoiseUnit :: Double
pNoiseUnit = 6.1

-- | A type representing @pNoise =~ -log(noise rate)@ of a ciphertext.
-- We use the promoted type @'PN@ of kind @PNoise@ to distinguish this value
-- from @Units@.
newtype PNoise = PN Nat

-- | Adds a @Nat@ to @PNoise@.
type family (:+) a b where
  'PN a :+ b = 'PN (a :+: b)

-- | A type representing the number of noise "units" in a modulus.
-- We use the promoted type @'Units@ of kind @Units@ to distinguish this
-- value from @PNoise@.
newtype Units = Units Nat

-- convenient synonym for Tagged. Useful for kind inference, and because we need
-- the partially applied "PNoiseTag p" type, which we can't write nicely with
-- 'Tagged' because it is in fact a type synonym.
-- | A value tagged by @pNoise =~ -log(noise rate)@.
newtype PNoiseTag (p :: PNoise) a = PTag {unPTag :: a}
  deriving (Additive.C, Ring.C, Functor, Show)

instance Applicative (PNoiseTag h) where
  pure = PTag
  (PTag f) <*> (PTag a) = PTag $ f a

-- | Convert a type natural to a TypeLit for nicer (type) error messages
type family NatToLit x where
  NatToLit 'Z = 0
  NatToLit ('S n) = 1 + (NatToLit n)

-- | A (nested pair of) modulus(i) having at least @h@ units, where a unit
-- is defined by the @pNoiseUnit@.
-- EAC: Add comment about generating with TH.
type family UnitsToModulus (h :: Units)

-- | The total noise units of the modulus @UnitsToModulus h@.
-- EAC: Add comment about generating with TH.
type family TotalUnits (h :: Units) :: Units

-- | Template Haskell splice to construct a Nat from an Int
natType :: Int -> TypeQ
natType x | x < 0 = error $ "natType: negative argument " ++ show x
natType 0 = conT 'Z
natType x = conT 'S `appT` (natType $ x-1)

natDec :: Int -> DecQ
natDec x = tySynD (mkName $ "N" ++ show x) [] $ natType x