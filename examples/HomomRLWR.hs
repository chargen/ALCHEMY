{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE RebindableSyntax      #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

{-# OPTIONS_GHC -fno-warn-partial-type-signatures #-}

module HomomRLWR where

import Crypto.Lol
import Crypto.Lol.Cyclotomic.Tensor.CPP

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
import Crypto.Alchemy.Interpreter.RescaleTree
import Crypto.Alchemy.Interpreter.Size
import Crypto.Alchemy.Language.Lambda hiding (s)
import Crypto.Alchemy.MonadAccumulator

import Control.Monad.Random
import Control.Monad.Writer

type K = P3
type Gad = TrivGad

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
{-
type instance UnitsToModulus ('Units N20) = Z6
type instance UnitsToModulus ('Units N21) = Z6
type instance UnitsToModulus ('Units N22) = Z6
type instance UnitsToModulus ('Units N23) = Z6
type instance UnitsToModulus ('Units N24) = Z6
-}

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
{-
type instance TotalUnits ('Units N20) = 'Units N24
type instance TotalUnits ('Units N21) = 'Units N24
type instance TotalUnits ('Units N22) = 'Units N24
type instance TotalUnits ('Units N23) = 'Units N24
type instance TotalUnits ('Units N24) = 'Units N24
-}

homomRLWR_5hop :: forall t rngs k outputPNoise env z2k expr z2 h0 h1 h2 h3 h4 h5 preTunnelPNoise postTunnelPNoise .
  (z2 ~ Z2E 'O,
   -- tunnel
   rngs ~ '[h0,h1,h2,h3,h4,h5],
   LinearChainCtx expr t postTunnelPNoise z2k rngs,
   PreLinearCycChain expr postTunnelPNoise rngs ~ preTunnelPNoise,
   -- rescaleCycCRT
   PreRescaleTreePow2 expr k (outputPNoise (Cyc t h5 z2)) ~ postTunnelPNoise (Cyc t h5 z2k),
   RescaleTreePow2Ctx expr k (outputPNoise (Cyc t h5 z2)))
  => Proxy rngs -> Tagged k (expr env (preTunnelPNoise (Cyc t h0 z2k) -> outputPNoise (Cyc t h5 z2)))
homomRLWR_5hop rngs = do
  rescaleTree <- rescaleTreePow2_ @(outputPNoise (Cyc t h5 z2))
  return $ rescaleTree .: linear5 rngs

main :: IO ()
main = do

  putStrLn "HomomRLWR:"
  let (ex21,ex22) = dup $ untag $ homomRLWR_5hop @CT @PTRngs @K @(PNoiseTag ('PN N0)) Proxy
  putStrLn $ "PT RLWR: " ++ pprint ex21
  putStrLn $ "PT RLWR size: " ++ show (size ex22)

  -- EAC: Could remove the type sig from ptrlwr and let it be inferred from the use of pt2ct below
  -- however, compiling the evalKeysHints block takes a long time, so it's convenient
  -- to comment it out and compile just the PT expression components faster.
  let (ptrlwr :: PT2CT' CTRngs Gad _, paramsexpr2) = dup $ untag $ homomRLWR_5hop @CT @PTRngs @K @(PNoiseTag ('PN N0)) Proxy
  putStrLn $ "PT expression params:\n" ++ params ptrlwr paramsexpr2
{-
  -- compile the un-applied function to CT, then print it out
  evalKeysHints 8.0 $ do

    rlwr <- timeIO "Compiling RLWR..." $
                   argToReader (pt2ct
                    @CTRngs
                    @Gad
                    @Int64)
                    --ptrlwr -- see comment above
                    (untag $ homomRLWR_5hop @CT @PTRngs @K @(PNoiseTag ('PN N0)) Proxy)

    let (r1,r)  = dup rlwr
        (r2,s)  = dup r
        (r3,t)  = dup s
        (r4,r5) = dup t

    liftIO $ putStrLn "Homom RLWR:"
    liftIO $ putStrLn $ pprint r1
    liftIO $ putStrLn $ params r1 r2
    liftIO $ putStrLn $ "Size: " ++ (show $ size r5)

    ptin <- liftIO $ getRandom
    arg1 <- argToReader encrypt ptin

    timeIO "Evaluating with error rates..." $ do
      f <- readerToAccumulator $ writeErrorRates @Int64 @() r3
      let (_,errors) = runWriter $ eval f (return arg1)
      liftIO $ print errors

    _ <- time "Evaluating without error rates..." $ eval r4 arg1

    liftIO $ putStrLn "Done."
-}