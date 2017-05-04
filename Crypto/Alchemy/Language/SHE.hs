{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}

module Crypto.Alchemy.Language.SHE where

import Crypto.Lol                      (Cyc, Factored)
import Crypto.Lol.Applications.SymmSHE (CT, KSQuadCircHint, SK, TunnelInfo)
import GHC.Exts

-- | Symantics for somewhat-homomorphic encryption operations (not
-- including those defined in 'Crypto.Alchemy.Language.Arithmetic').

class SHE expr where

  type ModSwitchPTCtx   expr ct zp'     :: Constraint
  type RescaleLinearCtx expr ct zq'     :: Constraint
  type AddPublicCtx     expr ct         :: Constraint
  type MulPublicCtx     expr ct         :: Constraint
  type KeySwitchQuadCtx expr ct zq' gad :: Constraint
  type TunnelCtx
    expr
    (t  :: Factored -> * -> *)
    (e  :: Factored) (r  :: Factored) (s  :: Factored)
    (e' :: Factored) (r' :: Factored) (s' :: Factored)
    zp zq gad :: Constraint

  modSwitchPT :: (ModSwitchPTCtx expr ct zp', ct ~ CT m zp (Cyc t m' zq))
    => expr env ct -> expr env (CT m zp' (Cyc t m' zq))

  rescaleLinear :: (RescaleLinearCtx expr ct zq', ct ~ CT m zp (Cyc t m' zq))
    => expr env (CT m zp (Cyc t m' zq')) -> expr env ct

  -- CJP: doesn't quite fall into addLit, though we could possibly
  -- generalize addLit to cover this (not clear if a good idea; this
  -- signature is pretty special)
  addPublic :: (AddPublicCtx expr ct, ct ~ CT m zp (Cyc t m' zq))
    => Cyc t m zp -> expr env ct -> expr env ct

  -- CJP: ditto here
  mulPublic :: (MulPublicCtx expr ct, ct ~ CT m zp (Cyc t m' zq))
    => Cyc t m zp -> expr env ct -> expr env ct

  keySwitchQuad :: (KeySwitchQuadCtx expr ct zq' gad, ct ~ CT m zp (Cyc t m' zq))
    => KSQuadCircHint gad (Cyc t m' zq') -> expr env ct -> expr env ct

  tunnel :: (TunnelCtx expr t e r s e' r' s' zp zq gad)
    => TunnelInfo gad t e r s e' r' s' zp zq
    -> expr env (CT r zp (Cyc t r' zq))
    -> expr env (CT s zp (Cyc t s' zq))

-- | Symantics for obtaining the error rate of a ciphertext.

class ErrorRate expr where

  type ErrorRateCtx expr ct z :: Constraint

  -- | Error rate of a ciphertext.  (Note that the secret key lives
  -- "outside" the object language.)
  errorRate :: (ErrorRateCtx expr ct z, ct ~ CT m zp (Cyc t m' zq))
            => SK (Cyc t m' z) -> expr e (ct -> Double)
