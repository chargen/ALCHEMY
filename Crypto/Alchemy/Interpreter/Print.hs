{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE UndecidableInstances  #-}

module Crypto.Alchemy.Interpreter.Print
( P, pprint
)
where

import Crypto.Alchemy.Interpreter.PT2CT.Noise
import Crypto.Alchemy.Language.Arithmetic
import Crypto.Alchemy.Language.Lambda
import Crypto.Alchemy.Language.LinearCyc
import Crypto.Alchemy.Language.List
import Crypto.Alchemy.Language.Monad
import Crypto.Alchemy.Language.Pair
import Crypto.Alchemy.Language.SHE
import Crypto.Alchemy.Language.String

import Crypto.Lol                      (Cyc, Linear, Pos (..), Prime2,
                                        PrimePower (..))
import Crypto.Lol.Applications.SymmSHE (CT)
import Crypto.Lol.Types

import Control.Monad.Reader            (MonadReader)
import Control.Monad.Writer            (MonadWriter)

-- the Int is the nesting depth of lambdas outside the expression
newtype P e a = P { unP :: Int -> String }

-- | Pretty-print a closed expression.
pprint :: P () a -> String
pprint = flip unP 0

pureP :: String -> P e a
pureP = P . const

-- | In the printout, variable indices grow "outside in," rather than
-- "inside out" (as in object-language code) because the
-- implementation is simpler that way.

instance Lambda_ P where
  lamDB f   = P $ \i -> "(\\v" ++ show  i ++ " -> " ++ unP f (i+1) ++ ")"
  f $: a    = P $ \i -> "("    ++ unP f i ++ " "    ++ unP a i     ++ ")"
  v0        = P $ \i -> "v" ++ show (i-1)
  weaken  v = P $ \i -> unP v (i-1)

instance List_ P where
  nil_  = pureP "nil"
  cons_ = pureP "cons"

instance Pair_ P where
  pair_ = pureP "pair"
  fst_  = pureP "fst"
  snd_  = pureP "snd"

instance String_ P where
  string_ = P . const

instance Add_ P a where
  add_ = pureP "add"
  neg_ = pureP "neg"

instance Show a => AddLit_ P a where
  addLit_ a = pureP $ "addLit (" ++ show a ++ ")"

instance Mul_ P a where
  type PreMul_ P a = a
  mul_ = pureP "mul"

instance Show a => MulLit_ P a where
  mulLit_ a = pureP $ "mulLit (" ++ show a ++ ")"

instance Div2_ P (Cyc t m (ZqBasic ('PP '(Prime2, k)) i)) where
  type PreDiv2_ P (Cyc t m (ZqBasic ('PP '(Prime2, k)) i)) =
    Cyc t m (ZqBasic ('PP '(Prime2, 'S k)) i)
  div2_ = pureP "div2"

instance Div2_ P (PNoiseCyc h t m (ZqBasic ('PP '(Prime2, k)) i)) where
  type PreDiv2_ P (PNoiseCyc h t m (ZqBasic ('PP '(Prime2, k)) i)) =
    PNoiseCyc h t m (ZqBasic ('PP '(Prime2, 'S k)) i)
  div2_ = pureP "div2"

instance Div2_ P (CT m (ZqBasic ('PP '(Prime2, k)) i) (Cyc t m' zq)) where
  type PreDiv2_ P (CT m (ZqBasic ('PP '(Prime2, k)) i) (Cyc t m' zq)) =
    CT m (ZqBasic ('PP '(Prime2, 'S k)) i) (Cyc t m' zq)

  div2_ = pureP "div2"

instance Functor_ P f where
  fmap_ = pureP "fmap"

instance Applicative_ P f where
  pure_ = pureP "pure"
  ap_   = pureP "ap"

instance Monad_ P m where
  bind_ = pureP "bind"

instance MonadReader r m => MonadReader_ P r m where
  ask_   = pureP "ask"
  local_ = pureP "local"

instance MonadWriter w m => MonadWriter_ P w m where
  tell_   = pureP "tell"
  listen_ = pureP "listen"
  pass_   = pureP "pass"

instance SHE_ P where

  type ModSwitchPTCtx_   P a zp' = ()
  type ModSwitchCtx_     P a zq' = ()
  type AddPublicCtx_     P (CT m zp (Cyc t m' zq)) = (Show (Cyc t m zp))
  type MulPublicCtx_     P (CT m zp (Cyc t m' zq)) = (Show (Cyc t m zp))
  type KeySwitchQuadCtx_ P a gad = ()
  type TunnelCtx_        P t e r s e' r' s' zp zq gad = ()

  modSwitchPT_     = pureP   "modSwitchPT"
  modSwitch_       = pureP   "modSwitch"
  addPublic_     p = pureP $ "addPublic (" ++ show p ++ ")"
  mulPublic_     p = pureP $ "mulPublic (" ++ show p ++ ")"
  keySwitchQuad_ _ = pureP   "keySwitchQuad <HINT>"
  tunnel_        _ = pureP   "tunnel <HINT>"

instance LinearCyc_ P (Linear t) (Cyc t) where
  type PreLinearCyc_ P (Cyc t) = Cyc t
  type LinearCycCtx_ P (Linear t) (Cyc t) e r s zp = ()

  linearCyc_ _ = pureP "linearCyc <FUNC>"

instance LinearCyc_ P (Linear t) (PNoiseCyc p t) where
  type PreLinearCyc_ P (PNoiseCyc p t) = PNoiseCyc p t
  type LinearCycCtx_ P (Linear t) (PNoiseCyc p t) e r s zp = ()

  linearCyc_ _ = pureP "linearCyc <FUNC>"

instance ErrorRate_ P where
  type ErrorRateCtx_ P ct z = ()
  errorRate_ _ = pureP "errorRate <KEY>"
