{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeFamilyDependencies #-}

module Crypto.Alchemy.Language.LinearCyc where

import Crypto.Alchemy.Language.Lambda
import Crypto.Lol.Factored
import GHC.Exts                       (Constraint)

-- | Symantics for evaluating a linear function on cyclotomics.

-- TODO: once Lol upgrade is in place, remove lin and use Linear explicitly?
class LinearCyc expr lin cyc | cyc -> lin where

  -- | Constraints needed to linear
  type LinearCycCtx expr lin cyc
       (e :: Factored) (r :: Factored) (s :: Factored) zp :: Constraint

  -- | 'Cyc' wrapper for the input to linearCyc_
  type PreLinearCyc expr cyc :: Factored -> * -> *

  -- | An object-language expression representing the given linear function.
  linearCyc_ :: (LinearCycCtx expr lin cyc e r s zp)
    => lin zp e r s             -- TODO: put zp last to match Lol upgrade
    -> expr env (PreLinearCyc expr cyc r zp -> cyc s zp)

linearCyc :: (LinearCyc expr lin cyc, LinearCycCtx expr lin cyc e r s zp,
              Lambda expr)
  => lin zp e r s               -- TODO: put zp last to match Lol upgrade
  -> expr env (PreLinearCyc expr cyc r zp)
  -> expr env (cyc s zp)
linearCyc f a = linearCyc_ f $: a
