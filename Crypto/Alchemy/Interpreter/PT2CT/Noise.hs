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
--{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE UndecidableInstances       #-}

{-# OPTIONS_GHC -fno-warn-unused-binds  #-}

-- should be a hidden/internal module
module Crypto.Alchemy.Interpreter.PT2CT.Noise
( PNoise(..)--, PNoise2Nat
, Units(..), UnitsToNat
, (:+), NatToLit
, PNoiseTag(..),ZqPairsWithUnits, TotalUnits, MaxUnits) where

import           Algebra.Additive          as Additive (C)
import           Algebra.Ring              as Ring (C)
--import           Data.Functor.Trans.Tagged
--import           Data.Singletons.Prelude   hiding ((:<), (:+))
--import           Data.Singletons.Prelude.List (Sum, Maximum)
--import           Data.Singletons.TH        hiding ((:<))
import           Data.Type.Natural         hiding ((:+))
--import qualified GHC.TypeLits              as TL (Nat)
import           GHC.TypeLits              hiding (Nat)
--import           Language.Haskell.TH

--import Crypto.Lol.Reflects
--import Crypto.Lol.Types.Unsafe.ZqBasic

-- | A value tagged by @pNoise =~ -log(noise rate)@.
newtype PNoise = PN Nat

--type family PNoise2Nat (p :: PNoise) where
--  PNoise2Nat ('PN p) = p

type family (:+) a b where
  'PN a :+ b = 'PN (a :+: b)

newtype Units = Units Nat

type family UnitsToNat (u :: Units) where
  UnitsToNat ('Units h) = h

-- convenient synonym for Tagged. Useful for kind inference, and because we need
-- the partially applied "PNoiseTag p" type, which we can't write niceyl with
-- 'Tagged' because it is in fact a type synonym
newtype PNoiseTag (p :: PNoise) a = PTag {unPTag :: a}
  -- EAC: Okay to derive Functor and Applicative? It makes life easier because
  -- we can define a single instance (e.g., of E) rather than one for Identity
  -- and one for (PNoise h)
  deriving (Additive.C, Ring.C, Functor, Show)

instance Applicative (PNoiseTag h) where
  pure = PTag
  (PTag f) <*> (PTag a) = PTag $ f a

type family NatToLit x where
  NatToLit 'Z = 0
  NatToLit ('S n) = 1 + (NatToLit n)

-- | The number of noise units of the largest modulus among the first
-- of those that in total have at least @h@ units.
type family MaxUnits (h :: Units) :: Nat
  -- Maximum (MapNatOf (MapModulus (ZqsWithUnits zqs h)))

-- | For a list of moduli @zqs@, nested pairs representing moduli that
-- have a total of at least @h@ units.
type family ZqPairsWithUnits (h :: Units)
  -- List2Pairs (ZqsWithUnits zqs h)


-- | The total noise units among the first of the moduli having at
-- least @h@ units.
type family TotalUnits (h :: Units) :: Units
