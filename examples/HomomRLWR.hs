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

import Crypto.Lol hiding (Pos(..))
import Crypto.Lol.Cyclotomic.Tensor.CPP
import Crypto.Lol.Types

import Common
import LinearDec2CRT
import RescaleTree

import Crypto.Alchemy.MonadAccumulator
--import Crypto.Alchemy.Interpreter.DedupRescale
import Crypto.Alchemy.Interpreter.Depth
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
import Crypto.Alchemy.Language.Arithmetic
import Crypto.Alchemy.Language.Lambda
import Crypto.Alchemy.Language.LinearCyc

import Control.Monad.Identity
import Control.Monad.Random
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import Data.Type.Natural --hiding (Nat(S))
import qualified Data.Type.Natural as TN

type K = P3
type Gad = TrivGad
type RescaleM'Map = '[ '(H5,H5)]

type Z1 = Zq 1520064001
type Z2 = (Zq 3144961, Z1)
type Z3 = (Zq 5241601, Z2)
type Z4 = (Zq 7338241, Z3)
type Z5 = (Zq 1522160641, Z4)
type Z6 = (Zq 1529498881, Z5)

type instance MaxUnits ('Units M0) = M5
type instance MaxUnits ('Units M1) = M5
type instance MaxUnits ('Units M2) = M5
type instance MaxUnits ('Units M3) = M5
type instance MaxUnits ('Units M4) = M5
type instance MaxUnits ('Units M5) = M5
type instance MaxUnits ('Units M6) = M5
type instance MaxUnits ('Units M7) = M5
type instance MaxUnits ('Units M8) = M5
type instance MaxUnits ('Units M9) = M5
type instance MaxUnits ('Units M10) = M5
type instance MaxUnits ('Units M11) = M5
type instance MaxUnits ('Units M12) = M5
type instance MaxUnits ('Units M13) = M5
type instance MaxUnits ('Units M14) = M5
type instance MaxUnits ('Units M15) = M5
type instance MaxUnits ('Units M16) = M5
type instance MaxUnits ('Units M17) = M5
type instance MaxUnits ('Units M18) = M5
type instance MaxUnits ('Units M19) = M5

type instance ZqPairsWithUnits ('Units M0) = Z1
type instance ZqPairsWithUnits ('Units M1) = Z1
type instance ZqPairsWithUnits ('Units M2) = Z1
type instance ZqPairsWithUnits ('Units M3) = Z1
type instance ZqPairsWithUnits ('Units M4) = Z1
type instance ZqPairsWithUnits ('Units M5) = Z1
type instance ZqPairsWithUnits ('Units M6) = Z2
type instance ZqPairsWithUnits ('Units M7) = Z2
type instance ZqPairsWithUnits ('Units M8) = Z2
type instance ZqPairsWithUnits ('Units M9) = Z3
type instance ZqPairsWithUnits ('Units M10) = Z3
type instance ZqPairsWithUnits ('Units M11) = Z3
type instance ZqPairsWithUnits ('Units M12) = Z4
type instance ZqPairsWithUnits ('Units M13) = Z4
type instance ZqPairsWithUnits ('Units M14) = Z4
type instance ZqPairsWithUnits ('Units M15) = Z5
type instance ZqPairsWithUnits ('Units M16) = Z5
type instance ZqPairsWithUnits ('Units M17) = Z5
type instance ZqPairsWithUnits ('Units M18) = Z5
type instance ZqPairsWithUnits ('Units M19) = Z5

type instance TotalUnits ('Units M0) = 'Units M5 -- 0
type instance TotalUnits ('Units M1) = 'Units M5 -- 1
type instance TotalUnits ('Units M2) = 'Units M5 -- 2
type instance TotalUnits ('Units M3) = 'Units M5 -- 3
type instance TotalUnits ('Units M4) = 'Units M5 -- 4
type instance TotalUnits ('Units M5) = 'Units M5 -- 5
type instance TotalUnits ('Units M6) = 'Units M8 -- 6
type instance TotalUnits ('Units M7) = 'Units M8 -- 7
type instance TotalUnits ('Units M8) = 'Units M8 -- 8
type instance TotalUnits ('Units M9) = 'Units M11 -- 9
type instance TotalUnits ('Units M10) = 'Units M11 -- 10
type instance TotalUnits ('Units M11) = 'Units M11 -- 11
type instance TotalUnits ('Units M12) = 'Units M14 -- 12
type instance TotalUnits ('Units M13) = 'Units M14 -- 13
type instance TotalUnits ('Units M14) = 'Units M14 -- 14
type instance TotalUnits ('Units M15) = 'Units M19 -- 15
type instance TotalUnits ('Units M16) = 'Units M19 -- 16
type instance TotalUnits ('Units M17) = 'Units M19 -- 17
type instance TotalUnits ('Units M18) = 'Units M19 -- 18
type instance TotalUnits ('Units M19) = 'Units M19 -- 19

{-
  '(Z6 , N5, 'Units N24), -- 20
  '(Z6 , N5, 'Units N24), -- 21
  '(Z6 , N5, 'Units N24), -- 22
  '(Z6 , N5, 'Units N24), -- 23
  '(Z6 , N5, 'Units N24)] -- 24
-}
-- k = 4 => PN N9
-- k = 3 => PN N6
-- k = 2 => PN N3

main :: IO ()
main = do

  putStrLn "RescaleTree:"
  let (ex01,ex02) = dup $ untag $ rescaleTreePow2_ @(PNoiseTag ('PN M0) (Cyc CT H5 (ZqBasic PP2 Int64))) @K
  putStrLn $ "PT RescaleTree: " ++ pprint ex01
  putStrLn $ "PT RescaleTree size: " ++ show (size ex02)

  -- EAC: can remove type sig and use ptexpr as the argument to pt2ct below (which infers the signature),
  -- but this requires compiling PT2CT which takes a long time.
  let (ptrescale :: PT2CT' RescaleM'Map Gad _, paramsexpr1) = dup $ untag $ rescaleTreePow2_ @(PNoiseTag ('PN M0) (Cyc CT H5 (ZqBasic PP2 Int64))) @K
  putStrLn $ "PT expression params:\n" ++ params ptrescale paramsexpr1


  putStrLn "Tunnel:"
  -- EAC: 'Z noise is important here so that we can print the composition of P expr
  let (ex11,ex12) = dup $ linear5 @CT @PTRngs @(Z2E K) @(PNoiseTag ('PN M0)) Proxy
  putStrLn $ "PT Tunnel: " ++ pprint ex11
  putStrLn $ "PT Tunnel size: " ++ show (size ex12)

  -- EAC: This needs to have a non-zero output pNoise level!!
  -- EAC: can remove type sig and use ptexpr as the argument to pt2ct below (which infers the signature),
  -- but this requires compiling PT2CT which takes a long time.
  let (pttunnel :: PT2CT' CTRngs Gad _, paramsexpr2) = dup $ linear5 @CT @PTRngs @(Z2E K) @(PNoiseTag ('PN M6)) Proxy
  putStrLn $ "PT expression params:\n" ++ params pttunnel paramsexpr2

  putStrLn $ "PT Composition: " ++ pprint (ex01 .: ex11)
  putStrLn $ "PT Composition size:" ++ show (size (ex02 .: ex12))
{-
  -- compile the un-applied function to CT, then print it out
  evalKeysHints 8.0 $ do

    roundTree <- timeIO "Compiling rounding tree..." $
                   argToReader (pt2ct
                    @RescaleM'Map
                    @Zqs
                    @Gad
                    @Int64)
                    (untag $ rescaleTreePow2_ @(PNoiseTag ('PN N0) (Cyc CT H5 (ZqBasic PP2 Int64))) @K)

    tunn <- timeIO "Compiling tunnel sequence..." $
               argToReader (pt2ct
                  @CTRngs
                  @Zqs
                  @Gad
                  @Int64)
                  (linear5 @CT @PTRngs @(Z2E K) @(PNoiseTag ('PN N9)) Proxy)

    let (r1,r)  = dup roundTree
        (r2,r') = dup r
        (r3,r'') = dup r'
        (r4,r5) = dup r''
        (s1,s)  = dup tunn
        (s2,s') = dup s
        (s3,s'') = dup s'
        (s4,s5) = dup s''

    liftIO $ putStrLn "CT Tunneling:"
    liftIO $ putStrLn $ pprint s1
    liftIO $ putStrLn $ params s1 s2
    liftIO $ putStrLn $ "Size: " ++ (show $ size s5)

    liftIO $ putStrLn "CT Rounding Tree:"
    liftIO $ putStrLn $ pprint r1
    liftIO $ putStrLn $ params r1 r2
    liftIO $ putStrLn $ "Size: " ++ (show $ size r5)

    liftIO $ putStrLn "CT Composition:"
    liftIO $ putStrLn $ pprint (r1 .: s1)
    liftIO $ putStrLn $ "Size: " ++ (show $ size (r5 .: s5))

    ptin <- liftIO $ getRandom
    arg1 <- argToReader encrypt ptin

    timeIO "Evaluating with error rates..." $ do
      f <- readerToAccumulator $ writeErrorRates @Int64 @() r3
      g <- readerToAccumulator $ writeErrorRates @Int64 @() s3
      let (_,errors) = runWriter $ eval (f .: g) (return arg1)
      liftIO $ print errors

    _ <- time "Evaluating without error rates..." $ eval (r4 .: s4) arg1

    liftIO $ putStrLn "Done."

-}


{-

    -- example with rescale de-duplication when tunneling
  -- print the unapplied PT function

  putStrLn $ pprint $ untag $ khprf_0hop @CT @H0 @P3 @Identity @Int64
  let (ex01,ex0) = dup $ untag $ khprf_0hop @CT @H0 @P3 @(PNoise 'Z) @Int64
      (ex02,ex03) = dup ex0
  putStrLn $ "PT expression0: " ++ pprint ex01
  putStrLn $ "PT expression0 size: " ++ (show $ size ex02)
  putStrLn $ "PT expression0 depth: " ++ (show $ depth ex03)

  putStrLn $ pprint $ untag $ khprf_1hop @CT @H4 @H0 @P2 @Identity @Int64
  let (ex11,ex1) = dup $ untag $ khprf_1hop @CT @H4 @H0 @P2 @(PNoise 'Z) @Int64
      (ex12,ex13) = dup ex1
  putStrLn $ "PT expression1: " ++ pprint ex11
  putStrLn $ "PT expression1 size: " ++ (show $ size ex12)
  putStrLn $ "PT expression1 depth: " ++ (show $ depth ex13)

  putStrLn $ pprint $ untag $ khprf_1hop' @CT @H0 @H1 @P3 @(PNoise 'Z) @Int64
  putStrLn $ pprint $ untag $ khprf_1hop' @CT @H0 @H1 @P3 @Identity @Int64
  putStrLn $ pprint $ untag $ khprf_1hop'' @CT @H0 @H1 @P3 @(PNoise 'Z) @Int64
  putStrLn $ pprint $ untag $ khprf_1hop'' @CT @H0 @H1 @P3 @Identity @Int64
  putStrLn $ pprint $ untag $ khprf_5hop @CT @'[H0,H1,H2,H3,H4,H5] @P3 @Identity @Int64 Proxy


  -- EAC: It's terrible that we can't use Dup here: PreDiv2 P and PreDiv2 E disagree
  putStrLn $ pprint $ untag $ khprf_5hop @CT @'[H0,H1,H2,H3,H4,H5] @P3 @(PNoise 'Z) @Int64 Proxy
  putStrLn $ show $ eval (untag $ khprf_5hop @CT @'[H0,H1,H2,H3,H4,H5] @P3 @(PNoise 'Z) @Int64 Proxy) 2

    tunn <- argToReader (pt2ct
                         @RngList
                         @ZqList
                         @TrivGad
                         @Int64)
                         --(rescale4to2 @CT @H0 @(PNoise 'Z)) -- 1 minute, 8 sec
                         (untag $ khprf_0hop @CT @H0 @P2 @(PNoise 'Z) @Int64)
                         --(rescale4to2 @CT @H5 @(PNoise 'Z)) -- 1 minute, 8 sec
                         --(untag $ khprf_1hop @CT @H4 @H5 @P3 @(PNoise 'Z) @Int64)
                         --(untag $ khprf_5hop @CT @'[H0,H1,H2,H3,H4,H5] @P3 @(PNoise 'Z) @Int64 Proxy)






    y <- argToReader (pt2ct
                         @'[ '(H0,H0)]
                         @ZqList
                         @TrivGad
                         @Int64
                         @Double)
                         --(rescale4to2 @CT @H0 @(PNoise 'Z)) -- 1 minute, 8 sec
                         (untag $ khprf_0hop @CT @H0 @P2 @(PNoise 'Z) @Int64) -- 1 minute, 6 sec
                         --(untag $ khprf_1hop @CT @H4 @H5 @P3 @(PNoise 'Z) @Int64)
                         --(untag $ khprf_5hop @CT @'[H0,H1,H2,H3,H4,H5] @P3 @(PNoise 'Z) @Int64 Proxy)
    -- compile once, interpret with multiple ctexprs!!

    let (z1,z2) = dup y
    liftIO $ putStrLn $ pprint z1
    z2' <- readerToAccumulator $ writeErrorRates @Int64 @() z2
    let (z2'',errors) = runWriter $ eval z2' $ return 2
    liftIO $ putStrLn $ show z2''
    liftIO $ print errors
    --liftIO $ putStrLn $ pprint $ dedupRescale z2
-}




{-
khprf_5hop :: forall t rngs k outputPNoise i env z2k expr z2 h0 h1 h2 h3 h4 h5 preTunnelPNoise postTunnelPNoise .
  (z2 ~ Z2E 'O i,
   -- tunnel
   rngs ~ '[h0,h1,h2,h3,h4,h5],
   TunnelChainCtx expr t postTunnelPNoise z2k rngs,
   PreTunnelM expr postTunnelPNoise rngs ~ preTunnelPNoise,
   -- rescaleCycCRT
   PreRescaleTreePow2 expr k (outputPNoise (Cyc t h5 z2)) ~ postTunnelPNoise (Cyc t h5 z2k),
   RescaleTreePow2Ctx expr k (outputPNoise (Cyc t h5 z2)))
  => Proxy rngs -> Tagged k (expr env (preTunnelPNoise (Cyc t h0 z2k) -> outputPNoise (Cyc t h5 z2)))
khprf_5hop rngs = do
  rescaleTree <- rescaleTreePow2_ @(outputPNoise (Cyc t h5 z2))
  return $ rescaleTree .: tunn5 rngs

-- khprf_1hop', but without point-free style
khprf_1hop'' :: forall t h4 h5 k outputPNoise i env z2k expr z2 postTunnelPNoise preTunnelPNoise rngs .
  (z2 ~ Z2E 'O i,
    -- tunnel
   rngs ~ '[h4,h5], TunnelChainCtx expr t postTunnelPNoise z2k rngs,
   PreTunnelM expr postTunnelPNoise rngs ~ preTunnelPNoise,
   -- rescaleCycCRT
   PreRescaleTreePow2 expr k (outputPNoise (Cyc t h5 z2)) ~ postTunnelPNoise (Cyc t h5 z2k),
   RescaleTreePow2Ctx expr k (outputPNoise (Cyc t h5 z2)))
  => Tagged k (expr env (preTunnelPNoise (Cyc t h4 z2k) -> outputPNoise (Cyc t h5 z2)))
khprf_1hop'' = do
  rescaleTree <- rescaleTreePow2_ @(outputPNoise (Cyc t h5 z2))
  return $ lam $ rescaleTree $: (tunnelDecToCRT_ $: v0)

-- khprf_1hop, but with generalized tunneling constraints
khprf_1hop' :: forall t h4 h5 k outputPNoise i env z2k expr z2 postTunnelPNoise preTunnelPNoise rngs .
  (z2 ~ Z2E 'O i,
    -- tunnel
   rngs ~ '[h4,h5], TunnelChainCtx expr t postTunnelPNoise z2k rngs,
   PreTunnelM expr postTunnelPNoise rngs ~ preTunnelPNoise,
   -- rescaleCycCRT
   PreRescaleTreePow2 expr k (outputPNoise (Cyc t h5 z2)) ~ postTunnelPNoise (Cyc t h5 z2k),
   RescaleTreePow2Ctx expr k (outputPNoise (Cyc t h5 z2)))
  => Tagged k (expr env (preTunnelPNoise (Cyc t h4 z2k) -> outputPNoise (Cyc t h5 z2)))
khprf_1hop' = do
  rescaleTree <- rescaleTreePow2_ @(outputPNoise (Cyc t h5 z2))
  return $ rescaleTree .: tunnelDecToCRT_

khprf_1hop :: forall t h4 h5 k outputPNoise i env z2k expr z2 postTunnelPNoise preTunnelPNoise .
  (z2 ~ Z2E 'O i, Lambda expr,
    -- tunnel
   TunnelDecToCRTCtx expr postTunnelPNoise t h4 h5 z2k,
   PreTunnelCyc expr postTunnelPNoise ~ preTunnelPNoise,
   -- rescaleCycCRT
   PreRescaleTreePow2 expr k (outputPNoise (Cyc t h5 z2)) ~ postTunnelPNoise (Cyc t h5 z2k),
   RescaleTreePow2Ctx expr k (outputPNoise (Cyc t h5 z2)))
  => Tagged k (expr env (preTunnelPNoise (Cyc t h4 z2k) -> outputPNoise (Cyc t h5 z2)))
khprf_1hop = do
  rescaleTree <- rescaleTreePow2_ @(outputPNoise (Cyc t h5 z2))
  return $ rescaleTree .: tunnelDecToCRT_

khprf_0hop :: forall t h5 k outputPNoise i z2k env expr z2 postTunnelPNoise .
  (z2 ~ Z2E 'O i, Lambda expr,
   -- rescaleCycCRT
   PreRescaleTreePow2 expr k (outputPNoise (Cyc t h5 z2)) ~ postTunnelPNoise (Cyc t h5 z2k),
   RescaleTreePow2Ctx expr k (outputPNoise (Cyc t h5 z2)))
  => Tagged k (expr env (postTunnelPNoise (Cyc t h5 z2k) -> outputPNoise (Cyc t h5 z2)))
khprf_0hop = rescaleTreePow2_
-}
