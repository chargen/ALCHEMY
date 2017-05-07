{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}

module Crypto.Alchemy.Interpreter.DedupRescale
( DedupRescale, dedupRescale)
where

import Crypto.Alchemy.Language.Arithmetic
import Crypto.Alchemy.Language.Lambda
import Crypto.Alchemy.Language.List
import Crypto.Alchemy.Language.Monad
import Crypto.Alchemy.Language.SHE

import Crypto.Lol                      (Cyc)
import Crypto.Lol.Applications.SymmSHE (CT)
import Data.Typeable

-- unlike in section 2.4 of the lecture notes, we don't use a function
-- from the context to the value, because then *every* op would then
-- have to call rescaleCT (if there's a context) with the possible
-- exception of rescaleCT itself.  Here it is better to work
-- "bottom-up" rather than "top-down," by remembering whether each
-- subexpression was the result of a rescale or not.

data DedupRescale expr e a where
  -- Indicates that the expression is the result of a rescale from b
  -- to a; retains the pre-rescaled expression.
  Rescaled :: (Typeable b) => expr e b -> expr e a -> DedupRescale expr e a
  -- Generic case.
  DR :: expr e a -> DedupRescale expr e a

unDR :: DedupRescale expr e a -> expr e a
unDR (Rescaled _ a) = a
unDR (DR a) = a

-- | De-duplicate rescaling operations in an expression.
dedupRescale :: DedupRescale expr e a -> expr e a
dedupRescale = unDR

-- map, ignoring rescaling context
dedupMap :: (expr e a -> expr e b)
       -> DedupRescale expr e a -> DedupRescale expr e b
dedupMap f = DR . f . unDR


-- EAC: sharing implications?
-- consider: (\x -> rescaleDown x + (rescaleDown x*x)) (rescaleUp y)
-- if we simplify this to \y -> y + ((rescaleUp y)*(rescaleUp y)),
-- we rescaleUp twice (but remove the duplicate)

instance (Lambda expr) => Lambda (DedupRescale expr) where
  lam f = DR $ lam $ unDR f
  f $: a = DR $ unDR f $: unDR a
  v0  = DR v0
  s a = DR $ s $ unDR a

instance (List expr) => List (DedupRescale expr) where
  nil_  = DR nil_
  cons_ = DR cons_

instance (Add expr a) => Add (DedupRescale expr) a where
  add_ = DR add_
  neg_ = DR neg_

instance (AddLit expr a) => AddLit (DedupRescale expr) a where
  x >+: y = DR $ x >+: unDR y

instance (MulLit expr a) => MulLit (DedupRescale expr) a where
  x >*: y = DR $ x >*: unDR y

instance (Mul expr a) => Mul (DedupRescale expr) a where
  type PreMul (DedupRescale expr) a = PreMul expr a
  mul_ = DR mul_

instance (SHE expr) => SHE (DedupRescale expr) where

  type ModSwitchPTCtx (DedupRescale expr) ct zp' =
    (ModSwitchPTCtx expr ct zp')
  type RescaleLinearCtx (DedupRescale expr) (CT m zp (Cyc t m' zq)) zq' =
    (Typeable (CT m zp (Cyc t m' zq)),
     Typeable (CT m zp (Cyc t m' zq')),
     RescaleLinearCtx expr (CT m zp (Cyc t m' zq)) zq')
  type AddPublicCtx (DedupRescale expr) ct = (AddPublicCtx expr ct)
  type MulPublicCtx (DedupRescale expr) ct = (MulPublicCtx expr ct)
  type KeySwitchQuadCtx (DedupRescale expr) ct gad =
    (KeySwitchQuadCtx expr ct gad)
  type TunnelCtx    (DedupRescale expr) t e r s e' r' s' zp zq gad =
    (TunnelCtx expr t e r s e' r' s' zp zq gad)

  modSwitchPT = dedupMap modSwitchPT

  rescaleLinear :: forall ct zq' m zp t m' zq e .
    (RescaleLinearCtx (DedupRescale expr) ct zq', ct ~ CT m zp (Cyc t m' zq))
    => (DedupRescale expr) e (CT m zp (Cyc t m' zq'))
    -> (DedupRescale expr) e ct

  rescaleLinear (Rescaled y@(prev :: expr e ct') x) =
    -- first check if *this* rescale is a no-op
    case (eqT :: Maybe (CT m zp (Cyc t m' zq') :~: ct)) of
      -- if so, preserve the context
      (Just Refl) -> Rescaled y x
      -- if not, check if this rescale reverses the previous rescale
      Nothing -> case (eqT :: Maybe (ct' :~: ct)) of
        (Just Refl) -> DR prev
        -- previous op was a rescale, but from a different type than we need
        Nothing -> Rescaled x $ rescaleLinear x

  rescaleLinear (DR x) =
    -- also remove if the input and output types are the same
    case (eqT :: Maybe (CT m zp (Cyc t m' zq') :~: ct)) of
      (Just Refl) -> DR x
      Nothing -> Rescaled x $ rescaleLinear x

  addPublic = dedupMap . addPublic

  mulPublic = dedupMap . mulPublic

  keySwitchQuad = dedupMap . keySwitchQuad

  tunnel = dedupMap . tunnel

instance (Functor_ expr) => Functor_ (DedupRescale expr) where
  fmap_ = DR fmap_

instance (Applicative_ expr) => Applicative_ (DedupRescale expr) where
  pure_ = DR pure_
  ap_   = DR ap_

instance (Monad_ expr) => Monad_ (DedupRescale expr) where
  bind_ = DR bind_

instance (MonadReader_ expr) => MonadReader_ (DedupRescale expr) where
  ask_ = DR ask_
  local_ = DR local_

instance (MonadWriter_ expr) => MonadWriter_ (DedupRescale expr) where
  tell_ = DR tell_
  listen_ = DR listen_
