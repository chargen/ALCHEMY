{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE Rank2Types            #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module Crypto.Alchemy.Language.Lambda where

newtype (i # j) a = Comp { unComp :: i (j a) }

instance (Functor i, Functor j) => Functor (i # j) where
  fmap f x = Comp $ (f <$>) <$> unComp x

instance (Applicative i, Applicative j) => Applicative (i # j) where
  pure x = Comp $ pure $ pure x
  --f <*> x

-- | Symantics for functions and application.

class Lambda expr where
  -- | Lambda abstraction.
  lamDB :: expr (e,a) b -> expr e (a -> b)

  -- | Application.
  infixl 1 $:             -- ($) is infixr, but l is nicer for obj lang
  ($:) :: expr e (a -> b) -> expr e a -> expr e b

  -- | The zero'th (most-recently bound) variable.
  v0 :: expr (b,a) a

  -- | Extend environment.
  weaken  :: expr e a -> expr (e,x) a

lam :: Lambda expr => (forall x. expr (e,x) a -> expr (e,x) b) -> expr e (a -> b)
lam body = lamDB $ body v0

lamM :: (Functor f, Lambda expr) => (forall x. expr (e, x) a -> f (expr (e, x) b)) -> f (expr e (a -> b))
lamM body = lamDB <$> body v0

-- | Let-sharing.
let_ :: Lambda expr => expr e a -> (forall x. expr (e,x) a -> expr (e, x) b) -> expr e b
let_ a f = lam f $: a

-- | Composition.
infixr 9 .:
(.:) :: (Lambda expr) => expr e (b -> c) -> expr e (a -> b) -> expr e (a -> c)
f .: g = lam $ \x -> var f $: (var g $: var x)

class Extends m n where
  var :: Lambda expr => expr m a -> expr n a

instance {-# OVERLAPS #-} Extends m m where
  var = id

instance (Extends m n, x ~ (n, e)) => Extends m x where
  var = weaken . var

-- Some useful target language functions
const_ :: Lambda expr => expr e (a -> b -> a)
const_ = lam $ \x -> lam $ \_ -> var x

flip_ :: Lambda expr => expr e ((a -> b -> c) -> b -> a -> c)
flip_ = lam $ \f -> lam $ \x -> lam $ \y -> var f $: var y $: var x
