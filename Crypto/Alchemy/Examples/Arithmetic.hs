{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE RebindableSyntax    #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}

module Crypto.Alchemy.Examples.Arithmetic where

import Crypto.Alchemy.Interpreter.Dup
import Crypto.Alchemy.Interpreter.Eval
import Crypto.Alchemy.Interpreter.Print
import Crypto.Alchemy.Interpreter.Compiler.PNoise
import Crypto.Alchemy.Interpreter.Compiler.PT2CT

import Crypto.Alchemy.Language.Arithmetic
import Crypto.Alchemy.Language.Lambda
import Crypto.Alchemy.Language.Lit

import Crypto.Lol hiding (Pos(..))
import Crypto.Lol.Cyclotomic.Tensor.CPP
import Crypto.Lol.Types
--import Crypto.Lol.Cyclotomic.Tensor (TElt) -- EAC: I shouldn't need to explicitly import this
--import Crypto.Lol.Types.ZPP -- EAC: I shouldn't need to explicitly import this...

import Data.Type.Natural (Nat (Z))

-- EAC: We can get rid of signatures once #13524 is fixed (should be in 8.2)

-- we give a type signature for easy partial type application
pt1 :: forall b e expr a .
  (a ~ PreMul expr b, Mul expr b, Add expr a, DB expr a, Lambda expr)
  => expr e (a -> a -> b)
pt1 = lam $ lam $ v0 *: (v0 +: (s v0))

pt1' :: forall b e expr a .
  (a ~ PreMul expr b, Mul expr b, Add expr a, DB expr a, Lambda expr, Lit expr a)
  => a -> a -> expr e b
pt1' a b = pt1 $: lit a $: lit b

type Zq q = ZqBasic q Int64


type F = $(mkQ 100)

main :: IO ()
main = do
  let (exp1a, exp1b) = dup $ pt1 @(Cyc CT F4 (Zq 7), PNoise 'Z (Cyc CT F4 (Zq 7))) @()
      (exp2a, exp2b) = dup $ pt1' @(Cyc CT F4 (Zq 7), Cyc CT F4 (Zq 7)) @() (7,7) (11,11)

  -- print the unapplied PT function
  putStrLn $ pprint exp1a
  --putStrLn $ pprint exp1b
  -- apply the PT function to arguments, then print it out
  putStrLn $ pprint exp2a
  -- apply the PT function to arguments and evaluate the function
  putStrLn $ show $ eval exp2b
  -- compile the un-applied function to CT, then print it out
  (x,_) <- compile
         @'[ '(F4, F8) ]
         @'[ Zq $(mkQ 7), Zq $(mkQ 11) ]
         @(Zq $(mkQ 13))
         @TrivGad
         @Double
         1.0
         exp1b
  putStrLn $ pprint x