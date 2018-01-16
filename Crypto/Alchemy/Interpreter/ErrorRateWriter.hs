{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE NoImplicitPrelude          #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE UndecidableInstances       #-}

module Crypto.Alchemy.Interpreter.ErrorRateWriter2
( ErrorRateWriter, writeErrorRates, Monadify, ErrorRateLog )
where

import Control.Applicative
import Control.Monad.Reader
import Control.Monad.Writer
import Data.Typeable

import Crypto.Lol
import Crypto.Lol.Applications.SymmSHE (CT, SK)
import Crypto.Lol.Utils.ShowType

import           Crypto.Alchemy.Interpreter.KeysHints
import           Crypto.Alchemy.Language.Arithmetic
import           Crypto.Alchemy.Language.Lambda
import           Crypto.Alchemy.Language.List
import           Crypto.Alchemy.Language.Monad
import           Crypto.Alchemy.Language.Pair
import           Crypto.Alchemy.Language.SHE
import qualified Crypto.Alchemy.Language.String       as LS

import Crypto.Alchemy.Interpreter.Eval

-- | A transformer that additionally logs the sizes of the noise terms
-- of any ciphertexts created during interpretation.
newtype ErrorRateWriter
  expr                          -- | the underlying interpreter
  z                             -- | (phantom) integral type for secret keys
  k                             -- | (reader) monad that supplies the
                                -- keys for extracting error
  w                             -- | (writer) monad for logging error rates
  e                             -- | environment
  a                             -- | represented type
    = ERW { unERW :: k (expr (Monadify w e) (w (Monadify w a))) }

{--- EAC: can't make this injective because there's ambiguity involving `w`:-}
{--- Consider `m Bool -> m Bool`: this could be the result of-}
{--- `Monadify (m Bool ->) (m Bool)` or `Monadify m (Bool -> Bool)`-}
type family Monadify w a where
  Monadify w (a,b) = (Monadify w a, w (Monadify w b))
  Monadify w (a -> b) = Monadify w a -> w (Monadify w b)
  Monadify w a = a

type ErrorRateLog = [(String,Double)]

-- | Transform an expression into (a monadic) one that logs error
-- rates, where the needed keys are obtained from the monad.
writeErrorRates :: forall z e expr k w a .
  (MonadWriter ErrorRateLog w, MonadReader Keys k)
  => ErrorRateWriter expr z k w e a -> k (expr (Monadify w e) (w (Monadify w a)))
writeErrorRates = unERW

-- | Perform the action, then perform the action given by the result,
-- and return the (first) result.
after_ :: (Monad_ expr, Monad m) => expr e ((a -> m ()) -> m a -> m a)
after_ = lam $ lam $ bind_ $: v0 $:
         lam (bind_ $: (v2 $: v0) $:
               lam (return_ $: v1))

tellError :: forall w expr m zp t m' zq z e .
  (MonadWriter ErrorRateLog w, Show (ArgType zq),
   List expr, MonadWriter_ expr, ErrorRate expr, LS.String expr, Pair expr,
   ErrorRateCtx expr (CT m zp (Cyc t m' zq)) z) =>
   String -> SK (Cyc t m' z) -> expr e (CT m zp (Cyc t m' zq) -> w ())
tellError str sk = lam (tell_ $: (cons_ $: (pair_ $: (LS.string_ $ str ++ showType (Proxy::Proxy zq)) $: (errorRate_ sk $: v0)) $: nil_))
--


type WriteErrorCtx expr z k w ct t m m' zp zq =
  (MonadWriter ErrorRateLog w, MonadReader Keys k, Typeable (SK (Cyc t m' z)), 
   List expr, LS.String expr, Pair expr, MonadWriter_ expr, ErrorRate expr,
   ct ~ (CT m zp (Cyc t m' zq)), ErrorRateCtx expr ct z, Show (ArgType zq))

-- | Convert an object-language function to a (monadic) one that
-- writes the error rate of its ciphertext output.
liftWriteError :: forall expr z k w ct t m m' zp zq a e .
  (WriteErrorCtx expr z k w ct t m m' zp zq)
  => Proxy z
  -> String                     -- | annotation
  -> expr e (a -> ct)           -- | the function to lift
  -> k (expr e (w (a -> w ct)))
liftWriteError _ str f_ = do
    key :: Maybe (SK (Cyc t m' z)) <- lookupKey
    return $ return_ $: case key of
      Just sk -> lam $ after_ $: tellError str sk $: ((return_ .: (s f_)) $: v0)
      Nothing -> return_ .: f_

-- TODO: this is a hack; liftWriteError2 should be reimplemented without this
kleislify2 :: (Monad_ expr, Monad m) => expr e ((m a -> m b -> m c) -> a -> m (b -> m c)) 
kleislify2 = lam $ return_ .: lam (v0 .: return_) .: v0 .: return_

liftWriteError2 :: forall expr z k w ct t m m' zp zq a b e .
  (WriteErrorCtx expr z k w ct t m m' zp zq)
  => Proxy z
  -> String                     -- | annotation
  -> expr e (a -> b -> ct)      -- | the function to lift
  -> k (expr e (w (a -> w (b -> w ct))))

liftWriteError2 _ str f_ =
  let mf_ = liftA2_ $: s (s f_) -- shift because we use between lam/lam,v0/v1
  in do
    key :: Maybe (SK (Cyc t m' z)) <- lookupKey
    return $ return_ .: kleislify2 $: case key of
      Just sk -> lam $ lam $ after_ $: tellError str sk $: (mf_ $: v1 $: v0)
      Nothing -> liftA2_ $: f_

instance (WriteErrorCtx expr z k w ct t m m' zp zq, Add expr ct) =>
  Add (ErrorRateWriter expr z k w) (CT m zp (Cyc t m' zq)) where

  add_ = ERW $ liftWriteError2 (Proxy::Proxy z) "add_" add_

  neg_ = ERW $ liftWriteError (Proxy::Proxy z) "neg_" neg_

instance (WriteErrorCtx expr z k w ct t m m' zp zq, Mul expr ct,
          -- needed because PreMul could take some crazy form
          Monadify w (PreMul expr ct) ~ PreMul expr ct)
         => Mul (ErrorRateWriter expr z k w) (CT m zp (Cyc t m' zq)) where

  type PreMul (ErrorRateWriter expr z k w) (CT m zp (Cyc t m' zq)) =
    PreMul expr (CT m zp (Cyc t m' zq))

  mul_ = ERW $ liftWriteError2 (Proxy::Proxy z) "mul_" mul_

instance (WriteErrorCtx expr z k w ct t m m' zp zq, AddLit expr ct) =>
  AddLit (ErrorRateWriter expr z k w) (CT m zp (Cyc t m' zq)) where

  addLit_ = ERW . liftWriteError (Proxy::Proxy z) "addLit_" . addLit_

instance (WriteErrorCtx expr z k w ct t m m' zp zq, MulLit expr ct) =>
  MulLit (ErrorRateWriter expr z k w) (CT m zp (Cyc t m' zq)) where

  mulLit_ = ERW . liftWriteError (Proxy::Proxy z) "mulLit_" . mulLit_

instance (WriteErrorCtx expr z k w ct t m m' zp zq,
          Monadify w (PreDiv2 expr ct) ~ PreDiv2 expr ct, ct ~ CT m zp (Cyc t m' zq),
          Div2 expr ct, Applicative k)
  => Div2 (ErrorRateWriter expr z k w) (CT m zp (Cyc t m' zq)) where
  type PreDiv2 (ErrorRateWriter expr z k w) (CT m zp (Cyc t m' zq)) =
    PreDiv2 expr (CT m zp (Cyc t m' zq))

  div2_ = ERW $ liftWriteError (Proxy::Proxy z) "div2_" div2_

{------ TRIVIAL WRAPPER INSTANCES ------}

instance (Monad_ expr, Monad w, Applicative k)
  => Lambda (ErrorRateWriter expr z k w) where
  lam f  = ERW $ fmap ((return_ $:) . (.: return_) . lam) (unERW f)
  f $: x = ERW $ ((>>=:) <$> (unERW f)) <*> ((bind_ $:) <$> (unERW x))
  v0     = ERW $ pure v0
  s a    = ERW $ s <$> (unERW a)

instance (SHE expr, Applicative_ expr, Applicative k, Applicative w) =>
  SHE (ErrorRateWriter expr z k w) where

  type ModSwitchPTCtx   (ErrorRateWriter expr z k w) (CT m zp (Cyc t m' zq)) zp' =
    (WriteErrorCtx expr z k w (CT m zp' (Cyc t m' zq)) t m m' zp' zq,
     ModSwitchPTCtx expr (CT m zp (Cyc t m' zq)) zp')
  type ModSwitchCtx     (ErrorRateWriter expr z k w) (CT m zp (Cyc t m' zq)) zq' =
    (WriteErrorCtx expr z k w (CT m zp (Cyc t m' zq')) t m m' zp zq',
     ModSwitchCtx expr (CT m zp (Cyc t m' zq)) zq')
  type AddPublicCtx     (ErrorRateWriter expr z k w) (CT m zp (Cyc t m' zq))     =
    (WriteErrorCtx expr z k w (CT m zp (Cyc t m' zq)) t m m' zp zq,
     AddPublicCtx expr (CT m zp (Cyc t m' zq)))
  type MulPublicCtx     (ErrorRateWriter expr z k w) (CT m zp (Cyc t m' zq))     =
    (WriteErrorCtx expr z k w (CT m zp (Cyc t m' zq)) t m m' zp zq,
     MulPublicCtx expr (CT m zp (Cyc t m' zq)))
  type KeySwitchQuadCtx (ErrorRateWriter expr z k w) (CT m zp (Cyc t m' zq)) gad =
    (KeySwitchQuadCtx expr (CT m zp (Cyc t m' zq)) gad,
     WriteErrorCtx expr z k w (CT m zp (Cyc t m' zq)) t m m' zp zq)
  type TunnelCtx (ErrorRateWriter expr z k w) t e r s e' r' s' zp zq gad =
      (TunnelCtx expr t e r s e' r' s' zp zq gad,
       WriteErrorCtx expr z k w (CT s zp (Cyc t s' zq)) t s s' zp zq)

  modSwitchPT_   = ERW $ liftWriteError (Proxy::Proxy z) "modSwitchPT_" $ modSwitchPT_
  modSwitch_     = ERW $ liftWriteError (Proxy::Proxy z) "modSwitch_" $ modSwitch_
  addPublic_     = ERW . liftWriteError (Proxy::Proxy z) "addPublic_" . addPublic_
  mulPublic_     = ERW . liftWriteError (Proxy::Proxy z) "mulPublic_" . mulPublic_
  keySwitchQuad_ = ERW . liftWriteError (Proxy::Proxy z) "keySwitchQuad_" . keySwitchQuad_
  tunnel_        = ERW . liftWriteError (Proxy::Proxy z) "tunnel_" . tunnel_

instance (ErrorRate expr, Applicative k, MonadWriter ErrorRateLog w, MonadWriter_ expr) =>
  ErrorRate (ErrorRateWriter expr z k w) where

  type ErrorRateCtx (ErrorRateWriter expr z' k w) ct z = ErrorRateCtx expr ct z
  errorRate_  sk = ERW . pure $ return_ $: (return_ .: errorRate_ sk)
