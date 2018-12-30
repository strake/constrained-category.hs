module Control.Category.Constrained (Semigroupoid (..), Category (..), Groupoid (..), Valid, NT (..), mkNT', nt') where

import Control.Categorical.Functor (map)
import qualified Control.Category as Base
import qualified Control.Category.Groupoid as Base
import Data.Constraint.Lifting
import Data.Type.Coercion
import Data.Type.Equality

class Semigroupoid (s :: α -> α -> Type) where
    (∘) :: s b c -> s a b -> s a c

type family Valid (s :: α -> α -> Type) :: α -> Constraint

class Semigroupoid s => Category s where
    id :: Valid s a => s a a
    id = id' Dict

    id' :: Dict (Valid s a) -> s a a
    id' Dict = id

class Category s => Groupoid s where
    invert :: (Valid s a, Valid s b) => s a b -> s b a
    invert = invert' Dict Dict

    invert' :: Dict (Valid s a) -> Dict (Valid s b) -> s a b -> s b a
    invert' Dict Dict = invert

instance {-# INCOHERENT #-} Base.Category s => Semigroupoid s where (∘) = (Base..)
instance {-# INCOHERENT #-} (Base.Category s, Valid s ~ Unconstrained1) => Category s where id = Base.id
instance {-# INCOHERENT #-} (Base.Groupoid s, Valid s ~ Unconstrained1) => Groupoid s where invert = Base.invert

instance {-# INCOHERENT #-} (Category s, Valid s ~ Unconstrained1) => Base.Category s where
    id = id
    (.) = (∘)

instance {-# INCOHERENT #-} (Groupoid s, Valid s ~ Unconstrained1) => Base.Groupoid s where
    invert = invert

type instance Valid (:~:) = Unconstrained1
instance Category (:~:) where id = Refl
instance Groupoid (:~:) where invert Refl = Refl

type instance Valid (:~~:) = Unconstrained1
instance Category (:~~:) where id = HRefl
instance Groupoid (:~~:) where invert HRefl = HRefl

type instance Valid Coercion = Unconstrained1
instance Category Coercion where id = Coercion
instance Groupoid Coercion where invert Coercion = Coercion

instance Semigroupoid (,) where (_, c) ∘ (a, _) = (a, c)
instance Semigroupoid Const where _ ∘ Const a = Const a

type instance Valid (->) = Unconstrained1
type instance Valid (:-) = Unconstrained1
instance Category (->) where id = Base.id
instance Category (:-) where id = Base.id

newtype NT s f g = NT { nt :: ∀ a . Valid s a => s (f a) (g a) }

instance Semigroupoid s => Semigroupoid (NT s) where NT f ∘ NT g = NT (f ∘ g)

type instance Valid (NT s) = Endolifting (Valid s)
instance Category s => Category (NT s) where
    id' d = NT (id' (lift' d))

instance Groupoid s => Groupoid (NT s) where
    invert' ad bd (NT f) = NT (invert' (lift' ad) (lift' bd) f)

lift' :: c a => Dict (Lifting c d f) -> Dict (d (f a))
lift' d = map (go d) Dict
  where go :: Dict (Lifting c d f) -> c a :- d (f a)
        go d = withDict d lift

instance Semigroupoid k => Semigroupoid (Dual k) where
    Dual f ∘ Dual g = Dual (g ∘ f)

type instance Valid (Dual k) = Valid k
instance Category k => Category (Dual k) where
    id = Dual id

instance Groupoid k => Groupoid (Dual k) where
    invert = Dual ∘ invert ∘ dual

nt' :: NT s f g -> Dict (Valid s a) -> s (f a) (g a)
nt' (NT f) Dict = f

mkNT' :: (∀ a . Dict (Valid s a) -> s (f a) (g a)) -> NT s f g
mkNT' f = NT (f Dict)
