module Data.Functor.Constrained where

import qualified Control.Categorical.Functor as U
import Control.Category.Constrained
import qualified Data.Functor as Base

-- | Laws:
--
-- @
-- 'map' (f '∘' g) = 'map' f '∘' 'map' g
-- @
class (Semigroupoid s, Semigroupoid t) => SGM (s :: α -> α -> *) (t :: β -> β -> *) (f :: α -> β) where
    map :: s a b -> t (f a) (f b)

-- | Laws:
--
-- @
-- 'map' 'id' = 'id'
-- @
class (SGM s t f, Category s, Category t) => Functor s t f

type Endofunctor s = Functor s s

infixl 4 <$>
(<$>) :: SGM s (->) f => s a b -> f a -> f b
(<$>) = map

instance {-# INCOHERENT #-} Base.Functor f => SGM (->) (->) f where map = Base.fmap
instance {-# INCOHERENT #-} Base.Functor f => Functor (->) (->) f

instance SGM (:-) (->) Dict where map = U.map
instance Functor (:-) (->) Dict

instance (SGM s (->) f, Valid s ~ Unconstrained1) => SGM (NT s) (NT (->)) (Compose f) where
    map (NT f) = NT (\ (Compose x) -> Compose (map f x))
instance (Functor s (->) f, Valid s ~ Unconstrained1) => Functor (NT s) (NT (->)) (Compose f)

instance SGM (NT (->)) (NT (NT (->))) Compose where
    map (NT f) = NT (NT (\ (Compose x) -> Compose (f x)))
instance Functor (NT (->)) (NT (NT (->))) Compose

instance (SGM s (->) f, SGM s (->) g) => SGM s (->) (Sum f g) where
    map f (InL x) = InL (f <$> x)
    map f (InR y) = InR (f <$> y)
instance (Functor s (->) f, Functor s (->) g) => Functor s (->) (Sum f g)

instance SGM (NT (->)) (NT (->)) (Sum f) where
    map (NT f) = NT (\ case InL x -> InL x
                            InR y -> InR (f y))
instance Functor (NT (->)) (NT (->)) (Sum f)

instance SGM (NT (->)) (NT (NT (->))) Sum where
    map (NT f) = NT (NT (\ case InL x -> InL (f x)
                                InR y -> InR y))
instance Functor (NT (->)) (NT (NT (->))) Sum

instance (SGM s (->) f, SGM s (->) g) => SGM s (->) (Product f g) where
    map f (Pair x y) = Pair (f <$> x) (f <$> y)
instance (Functor s (->) f, Functor s (->) g) => Functor s (->) (Product f g)

instance SGM (NT (->)) (NT (->)) (Product f) where
    map (NT f) = NT (\ (Pair x y) -> Pair x (f y))
instance Functor (NT (->)) (NT (->)) (Product f)

instance SGM (NT (->)) (NT (NT (->))) Product where
    map (NT f) = NT (NT (\ (Pair x y) -> Pair (f x) y))
instance Functor (NT (->)) (NT (NT (->))) Product

instance Semigroupoid s => SGM s (->) (Const a) where
    map _ (Const a) = Const a
instance Category s => Functor s (->) (Const a)

instance SGM (->) (NT (->)) Const where
    map f = NT (\ (Const a) -> Const (f a))
instance Functor (->) (NT (->)) Const

instance SGM (->) (->) Identity where
    map f (Identity a) = Identity (f a)
instance Functor (->) (->) Identity

instance Semigroupoid s => SGM s (->) Proxy where
    map _ Proxy = Proxy
instance Category s => Functor s (->) Proxy

instance SGM (->) (->) ((,) a) where
    map f (a, b) = (a, f b)
instance Functor (->) (->) ((,) a)

instance SGM (->) (NT (->)) (,) where
    map f = NT (\ (a, b) -> (f a, b))
instance Functor (->) (NT (->)) (,)

instance SGM (->) (->) (Either a) where
    map _ (Left a) = Left a
    map f (Right b) = Right (f b)
instance Functor (->) (->) (Either a)

instance SGM (->) (NT (->)) Either where
    map f = NT (\ case Left a -> Left (f a)
                       Right b -> Right b)
instance Functor (->) (NT (->)) Either

instance Semigroupoid s => SGM s (->) (s a) where map = (∘)
instance Category s => Functor s (->) (s a)

instance Semigroupoid s => SGM (Dual s) (NT (->)) s where map (Dual f) = NT (∘ f)
instance Category s => Functor (Dual s) (NT (->)) s
