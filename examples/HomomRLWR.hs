{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE NoImplicitPrelude         #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE PartialTypeSignatures     #-}
{-# LANGUAGE TemplateHaskell           #-}
{-# LANGUAGE TypeApplications          #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE TypeOperators             #-}

{-# OPTIONS_GHC -fno-warn-partial-type-signatures #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures #-}

module HomomRLWR where

import Control.Monad.Random
import Data.Functor                         ((<$>))
import Data.Maybe                           (fromJust)

import Crypto.Alchemy
import Crypto.Alchemy.Language.RescaleTree
import Crypto.Lol.Applications.SymmSHE      (mulPublic)
import Crypto.Lol
import Crypto.Lol.Cyclotomic.Tensor.CPP

import Common

type M'Map = '[ '(H0,H0')
              , '(H1,H1')
              , '(H2,H2')
              , '(H3,H3')
              , '(H4,H4')
              , '(H5,H5')
              ]

type Zqs = '[ Zq $(mkTLNatNat 1520064001) -- last mul: > 2^30.5
            , Zq $(mkTLNatNat 649958401)  -- 3 rounding muls: > 2^19 (larger than they 
            , Zq $(mkTLNatNat 707091841)  -- strictly need to be to account for 
            , Zq $(mkTLNatNat 742210561)  -- the mulPublic)
            , Zq $(mkTLNatNat 1522160641) -- fit 5 hops: > (last mul)
            , Zq $(mkTLNatNat 1529498881) -- extra for KS: big
            ]

type K = P5
type Gad = TrivGad
type PT = PNoiseCyc PNZ CT H5 (Zq PP2)

ringRound :: _ => expr env (_ -> PT)
ringRound =  untag (rescaleTreePow2_ @K) .: tunnel5

homomRingRound = pt2ct @M'Map @Zqs @Gad @Int64 ringRound

homomRLWR = do
  s <- getRandom
  (f, keys, _) <- runKeysHints 8.0 $
    liftM2 (.) (eval <$> homomRingRound) $
               flip mulPublic <$> encrypt s
  return (f, s, keys)


main :: IO ()
main = do
  (f, s, keys) <- timeIO "Generating function... " homomRLWR

  a <- getRandom
  ptResult  <- time "Computing plaintext result... " $ unPNC $ eval ringRound (PNC $ s * a)
  encResult <- time "Computing encrypted result... " $ f a

  let decResult = fromJust $ decrypt encResult keys
  putStrLn $ if decResult == ptResult then "PASS" else "FAIL"
