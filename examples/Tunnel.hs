{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PartialTypeSignatures      #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE RebindableSyntax           #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}

{-# OPTIONS_GHC -fno-warn-partial-type-signatures #-}

module Tunnel where

import Control.Monad.Identity
import Control.Monad.IO.Class
import Control.Monad.Random
import Control.Monad.Writer

import Common
import LinearDec2CRT
import Crypto.Alchemy.Interpreter.Dup
import Crypto.Alchemy.Interpreter.ErrorRateWriter
import Crypto.Alchemy.Interpreter.Eval
import Crypto.Alchemy.Interpreter.KeysHints
import Crypto.Alchemy.Interpreter.Params
import Crypto.Alchemy.Interpreter.Print
import Crypto.Alchemy.Interpreter.PT2CT
import Crypto.Alchemy.Interpreter.PT2CT.Noise
import Crypto.Alchemy.MonadAccumulator

import Crypto.Lol hiding (Pos(..))
import Crypto.Lol.Cyclotomic.Tensor.CPP

type Gad = BaseBGad 2

type Z1 = Zq 1520064001
type Z2 = (Zq 3144961, Z1)
type Z3 = (Zq 5241601, Z2)
type Z4 = (Zq 7338241, Z3)
type Z5 = (Zq 1522160641, Z4)
type Z6 = (Zq 1529498881, Z5)

type instance UnitsToModulus ('Units N0) = Z1
type instance UnitsToModulus ('Units N1) = Z1
type instance UnitsToModulus ('Units N2) = Z1
type instance UnitsToModulus ('Units N3) = Z1
type instance UnitsToModulus ('Units N4) = Z1
type instance UnitsToModulus ('Units N5) = Z1
type instance UnitsToModulus ('Units N6) = Z2
type instance UnitsToModulus ('Units N7) = Z2
type instance UnitsToModulus ('Units N8) = Z2
type instance UnitsToModulus ('Units N9) = Z3
type instance UnitsToModulus ('Units N10) = Z3
type instance UnitsToModulus ('Units N11) = Z3
type instance UnitsToModulus ('Units N12) = Z4
type instance UnitsToModulus ('Units N13) = Z4
type instance UnitsToModulus ('Units N14) = Z4
type instance UnitsToModulus ('Units N15) = Z5
type instance UnitsToModulus ('Units N16) = Z5
type instance UnitsToModulus ('Units N17) = Z5
type instance UnitsToModulus ('Units N18) = Z5
type instance UnitsToModulus ('Units N19) = Z5

type instance TotalUnits ('Units N0) = 'Units N5
type instance TotalUnits ('Units N1) = 'Units N5
type instance TotalUnits ('Units N2) = 'Units N5
type instance TotalUnits ('Units N3) = 'Units N5
type instance TotalUnits ('Units N4) = 'Units N5
type instance TotalUnits ('Units N5) = 'Units N5
type instance TotalUnits ('Units N6) = 'Units N8
type instance TotalUnits ('Units N7) = 'Units N8
type instance TotalUnits ('Units N8) = 'Units N8
type instance TotalUnits ('Units N9) = 'Units N11
type instance TotalUnits ('Units N10) = 'Units N11
type instance TotalUnits ('Units N11) = 'Units N11
type instance TotalUnits ('Units N12) = 'Units N14
type instance TotalUnits ('Units N13) = 'Units N14
type instance TotalUnits ('Units N14) = 'Units N14
type instance TotalUnits ('Units N15) = 'Units N19
type instance TotalUnits ('Units N16) = 'Units N19
type instance TotalUnits ('Units N17) = 'Units N19
type instance TotalUnits ('Units N18) = 'Units N19
type instance TotalUnits ('Units N19) = 'Units N19

main :: IO ()
main = do
  let (exp1a, exp2a) = dup $ linear2 @CT @H0 @H1 @H2 @(Zq PP8) @Identity Proxy

  -- example with rescale de-duplication when tunneling
  -- print the unapplied PT function
  putStrLn $ pprint exp1a
  putStrLn $ show $ eval exp2a 2


  let ptexpr = linear2 @CT @H0 @H1 @H2 @(Zq PP8) @(PNoiseTag ('PN N0)) Proxy :: PT2CT' RngList Gad _
  --let ptexpr = linear5 @CT @'[H0,H1,H2,H3,H4,H5] @(Zq PP8) @(PNoise 'Z) Proxy
  putStrLn $ "PT expression params:\n" ++ (params ptexpr $ linear2 @_ @_ @H1 Proxy)

  pt1 <- getRandom

  -- compile the up-applied function to CT, then print it out
  evalKeysHints 8.0 $ do
    y <- argToReader (pt2ct
         @RngList
         @Gad
         @Int64)
         (linear2 @CT @H0 @H1 @H2 @(Zq PP8) @(PNoiseTag ('PN N0)) Proxy)
         --(tunn5 @CT @'[H0,H1,H2,H3,H4,H5] @(Zq PP8) @(PNoise 'Z) Proxy)
    -- compile once, interpret with multiple ctexprs!!
    let (z1,z2) = dup y
        (w1,w2) = dup z1
    liftIO $ putStrLn $ pprint w1
    liftIO $ putStrLn $ params w1 w2
    arg1 <- argToReader encrypt pt1

    z2' <- readerToAccumulator $ writeErrorRates @Int64 @() z2
    let (_,errors) = runWriter $ eval z2' $ return arg1
    liftIO $ print $ "Error rates: " ++ show errors
    --liftIO $ putStrLn $ pprint $ dedupRescale z2

type RngList = '[ '(H0,H0'), '(H1,H1'), '(H2,H2')] -- , '(H3,H3'), '(H4,H4'), '(H5,H5') ]
