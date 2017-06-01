{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE RebindableSyntax      #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}

{-# OPTIONS_GHC -fno-warn-partial-type-signatures #-}

module Arithmetic where

import Common

import Control.Monad.Reader
import Control.Monad.Writer

import Crypto.Alchemy.MonadAccumulator
import Crypto.Alchemy.Interpreter.Depth
import Crypto.Alchemy.Interpreter.Dup
import Crypto.Alchemy.Interpreter.ErrorRateWriter
import Crypto.Alchemy.Interpreter.Eval
import Crypto.Alchemy.Interpreter.KeysHints
import Crypto.Alchemy.Interpreter.Params
import Crypto.Alchemy.Interpreter.Print
import Crypto.Alchemy.Interpreter.PT2CT
import Crypto.Alchemy.Interpreter.PT2CT.Noise
import Crypto.Alchemy.Interpreter.Size

import Crypto.Alchemy.Language.Arithmetic
import Crypto.Alchemy.Language.Lambda

import Crypto.Lol                       hiding (Pos (..))
import Crypto.Lol.Cyclotomic.Tensor.CPP

import Control.Applicative
import Control.Monad.Random
import Data.Maybe

-- EAC: We can get rid of signatures once #13524 is fixed (should be in 8.2)

-- we give a type signature for easy partial type application
{-
addMul :: forall a e expr .
  (Add expr a, Lambda expr)
  => expr e (a -> a -> a)
addMul = lam $ lam $ v0 +: v0
-}
addMul :: forall b e expr a .
  (a ~ PreMul expr b, Mul expr b, Add expr a, Lambda expr)
  => expr e (a -> a -> b)
addMul = lam $ lam $ v0 *: (v0 +: v1)

{-
addMul :: forall a e expr .
  (Add expr a, Lambda expr)
  => expr e (a -> a -> a)
addMul = lam $ lam $ (lam $ v0 +: v0) $: (v1 +: v0)
-}
type M = F512
type M'Map = '[ '(F4, M) ]
--type Zqs = '[Zq $(mkTLNatNat 268440577), Zq $(mkTLNatNat 8392193), Zq $(mkTLNatNat 1073750017)] -- ,1073753089)]


type Z1 = Zq 268440577
type Z2 = (Zq 8392193,Z1)
type Z3 = (Zq 1073750017,Z2)

type instance UnitsToModulus ('Units N0) = Z1
type instance UnitsToModulus ('Units N1) = Z1
type instance UnitsToModulus ('Units N2) = Z1
type instance UnitsToModulus ('Units N3) = Z1
type instance UnitsToModulus ('Units N4) = Z1
type instance UnitsToModulus ('Units N5) = Z2
type instance UnitsToModulus ('Units N6) = Z2
type instance UnitsToModulus ('Units N7) = Z2
type instance UnitsToModulus ('Units N8) = Z3
type instance UnitsToModulus ('Units N9) = Z3
type instance UnitsToModulus ('Units N10) = Z3
type instance UnitsToModulus ('Units N11) = Z3

type instance TotalUnits ('Units N0) = 'Units N4
type instance TotalUnits ('Units N1) = 'Units N4
type instance TotalUnits ('Units N2) = 'Units N4
type instance TotalUnits ('Units N3) = 'Units N4
type instance TotalUnits ('Units N4) = 'Units N4
type instance TotalUnits ('Units N5) = 'Units N7
type instance TotalUnits ('Units N6) = 'Units N7
type instance TotalUnits ('Units N7) = 'Units N7
type instance TotalUnits ('Units N8) = 'Units N11
type instance TotalUnits ('Units N9) = 'Units N11
type instance TotalUnits ('Units N10) = 'Units N11
type instance TotalUnits ('Units N11) = 'Units N11

main :: IO ()
main = do
  -- no types needed to show a function!
  putStrLn $ "PT expression: " ++ pprint addMul

  putStrLn $ "PT expression size: " ++ show (size addMul)
  putStrLn $ "Expression depth: "   ++ show (depth addMul)
  -- evaluate a DSL function to a Haskell function, then apply to arguments
  pt1 <- getRandom
  pt2 <- getRandom
  let ptresult = eval (addMul @(Cyc CT F4 (Zq 7))) pt1 pt2
  putStrLn $ "PT evaluation result: " ++ show ptresult

  -- EAC: can remove type sig and use ptexpr as the argument to pt2ct below (which infers the signature),
  -- but this requires compiling PT2CT which takes a long time.
  let ptexpr = addMul @(PNoiseTag ('PN N0) (Cyc CT F4 (Zq 7))) ::  PT2CT' M'Map TrivGad _
  putStrLn $ "PT expression params:\n" ++ params ptexpr addMul

  evalKeysHints (8.0 :: Double) $ do

    -- compile the un-applied function to CT, then print it out
    x <- argToReader (pt2ct
           @M'Map
           @TrivGad -- (BaseBGad 2)
           @Int64)
           (addMul @(PNoiseTag ('PN N0) (Cyc CT F4 (Zq 7))))

    -- duplicate the compiled expression
    let (z1,z2) = dup x
        (w1,w2) = dup z1
    -- encrypt some arguments
    arg1 <- argToReader encrypt pt1
    arg2 <- argToReader encrypt pt2
    -- print the compiled function
    liftIO $ putStrLn $ "CT expression: " ++ pprint w1
    liftIO $ putStrLn $ "CT expression params:\n" ++ params w1 w2
    --liftIO $ putStrLn $ "CT expression size: " ++ (show $ size w2)

    z2' <- readerToAccumulator $ writeErrorRates @Int64 @() z2
    let (result,errors) = runWriter $ eval z2' (return arg1) (return arg2)
    liftIO $ print $ "Error rates: " ++ show errors

    -- show the encrypted result
    --liftIO $ putStrLn $ "Encrypted evaluation result: " ++ show result
    -- show the decrypted result
    decResult <- fromJust <$> readerToAccumulator (decrypt result)
    liftIO $ putStrLn $ "Decrypted evaluation result: " ++ show decResult

    liftIO $ putStrLn $ if decResult == ptresult then "PASS" else "FAIL"


{-
-- direct SHE computation
  pt :: PT (Cyc CT F4 (Zq 7))  <- getRandom
  sk :: SK (Cyc CT M Int64) <- genSK (0.01 :: Double)
  ct :: SHE.CT F4 (Zq 7) (Cyc CT M (Zq $(mkTLNatNat 268440577))) <-
                 SHE.encrypt sk pt

  let ct' = modSwitch (ct*ct) :: SHE.CT F4 (Zq 7) (Cyc CT M (Zq $(mkTLNatNat 268440577), Zq $(mkTLNatNat 36095)))

  --print $ show ct
  print $ errorRate sk ct
  print $ errorRate sk (ct*ct)
  print $ errorRate sk ct'
  --print $ show $ ct+ct
  print $ errorRate sk (ct'+ct')
  let pt' = pt*pt
  print $ show $ pt' == (SHE.decryptUnrestricted sk ct')
  print $ show $ (pt'+pt') == (SHE.decryptUnrestricted sk (ct'+ct'))



errorRate :: forall t m' m z zp zq ct .
  (ErrorTermUCtx t m' z zp zq, Mod zq, ToInteger (LiftOf zq), ct ~ SHE.CT m zp (Cyc t m' zq))
  => SK (Cyc t m' z) -> ct -> Double
errorRate sk ct =
  (fromIntegral $ maximum $ fmap abs $ errorTermUnrestricted sk ct) / (fromIntegral $ proxy modulus (Proxy::Proxy zq))
-}
