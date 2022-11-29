-- singletons-ski

{-# LANGUAGE GHC2021 #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wall -Wno-unticked-promoted-constructors -Wno-redundant-constraints #-}

import Data.Kind (Type, Constraint)
import Unsafe.Coerce (unsafeCoerce)
import Data.Proxy (Proxy)
import Data.Coerce (Coercible)
import Data.Type.Equality ((:~:)(Refl))

-- Helpers

type CoerceTo' :: forall a b. a :~: b -> a -> b
type family CoerceTo' (eq :: a :~: b) (x :: a) :: b where
  CoerceTo' 'Refl x = x

type Representational :: (a -> b) -> Constraint
type Representational f = (forall x y. Coercible x y => Coercible (f x) (f y))

type family Skolem :: a where

-- Singleton classes

-- LAW: Coercible (Single @a) a
type Single :: forall (a :: Type). a -> Type
data family Single :: a -> Type

unSingle :: Single (x :: a) -> a
unSingle = unsafeCoerce

unSingle' :: forall f a x. Representational f => f (Single (x :: a)) -> f a
unSingle' = unsafeCoerce

single :: a -> (Single (x :: a) -> b) -> b
single x f = f (unsafeCoerce x)

single' :: forall f a x b. Representational f => f a -> (f (Single (x :: a)) -> b) -> b
single' x f = f (unsafeCoerce x)

newtype H1 a c b = H1 (c a => b)

unsafeSingleConstraint ::
  forall (a :: Type) (c :: Type -> Constraint) (b :: Type) (x :: a).
  Proxy c -> (c (Single (x :: a)) => b) -> c a => b
unsafeSingleConstraint _ f = unsafeCoerce (H1 f :: H1 (Single x) c b)

unsafeUnSingleConstraint ::
  forall (a :: Type) (c :: Type -> Constraint) (b :: Type) (x :: a).
  Proxy c -> (c a => b) -> c (Single x) => b
unsafeUnSingleConstraint _ f = unsafeCoerce (H1 f :: H1 a c b)

type family MkSingle :: forall (x :: a) -> Single x where

type UnSingle :: forall (a :: Type) (x :: a). Single x -> a
type family UnSingle (sx :: Single (x :: a)) :: a where
  UnSingle @_ @x _ = x

sinst :: forall (a :: Type) (f :: a -> Type) (y :: forall z. f z) (x :: a). Single @(forall z. f z) y -> Single @(f x) y
sinst x = unsafeCoerce x

class Known (x :: a) where
  known :: Single x

known' :: forall {a} (x :: a). Known x => Proxy x -> a
known' _ = unSingle $ known @a @x

newtype H2 (x :: a) b = H2 (Known x => b)

know :: forall (a :: Type) (b :: Type) (x :: a). Single x -> (Known x => b) -> b
know x f = unsafeCoerce (H2 f :: H2 x b) x

instance Show a => Show (Single (x :: a)) where
  showList = showList . unSingle'
  show = show . unSingle
  showsPrec n = showsPrec n . unSingle

-- Data types

data instance Single @Bool b where
  SFalse :: Single 'False
  STrue :: Single 'True
instance Known False where
  known = SFalse
instance Known True where
  known = STrue

data instance Single @() u where
  SUnit :: Single '()
instance Known '() where
  known = SUnit

data instance Single @(a, b) p where
  SPair :: Single x -> Single y -> Single '(x, y)
instance (Known x, Known y) => Known '(x, y) where
  known = SPair known known

data instance Single @(Either a b) e where
  SLeft :: Single x -> Single (Left x)
  SRight :: Single y -> Single (Right y)
instance Known x => Known (Left x) where
  known = SLeft known
instance Known y => Known (Right y) where
  known = SRight known

data Some (f :: a -> Type) = forall (x :: a). Some (f x)
data instance Single @(Some f) s where
  SSome :: forall f x (y :: f x). Single @(f x) y -> Single ('Some y)
instance forall a (f :: a -> Type) (x :: a) (y :: f x). Known y => Known ('Some y) where
  known = SSome known

data Forall (f :: a -> Type) = Forall (forall (x :: a). f x)
data instance Single @(Forall (f :: a -> Type)) fl where
  SForall ::
    forall (a :: Type) (f :: a -> Type) (y :: forall (x :: a). f x).
    Single @(forall (x :: a). f x) y -> Single ('Forall y)
instance forall a (f :: a -> Type) (y :: forall x. f x). (forall x. Known (y @x)) => Known ('Forall y) where
  known = SForall $ unsafeCoerce (known :: Single (y @Skolem))

-- Isomorphic to 'Forall' on the term-level.
-- Not isomorphic on the type-level, but viewed externally is equivalent.
-- ((forall x. f x) -> ForallS f, forall x. ForallS f -> f x)
data ForallS (f :: a -> Type) = forall b. ForallS (forall (x :: a). b ~> f x) b
data instance Single @(ForallS (f :: a -> Type)) fl where
  SForallS ::
    forall a b (f :: a -> Type) (y :: forall (x :: a). b ~> f x) (z :: b).
    Single @(forall (x :: a). b ~> f x) y -> Single z -> Single ('ForallS y z)
instance
  forall a b (f :: a -> Type) (y :: forall x. b ~> f x) (z :: b).
  (Known z, forall x. Known (y @x)) => Known ('ForallS y z) where
    known = SForallS (unsafeCoerce (known :: Single (y @Skolem))) known

newtype Fix (f :: Type -> Type) = Fix (f (Fix f))
data instance Single @(Fix f) fx where
  SFix :: Single @(f (Fix f)) x -> Single ('Fix x)
instance Known x => Known ('Fix x) where
  known = SFix known

-- Type-level Newtype-specialised generics

type family DefineNewtypeInner (a :: Type) :: Type
type family GetNewtypeInner (a :: Type) :: Type where
  GetNewtypeInner a = DefineNewtypeInner a

{- FIXME: doesn't work with type-level SKI definitions for some reason
type family GetNewtypeInner' (rep :: Type -> Type) :: Type where
  GetNewtypeInner' (D1 ( 'MetaData _ _ _ 'True) (C1 _ (S1 _ (Rec0 (x :: Type))))) = x

type family GetNewtypeInner (a :: Type) :: Type where
  GetNewtypeInner x = GetNewtypeInner' (Rep x)
-}

type family DefineNewtypeConstructor (a :: Type) :: inner -> a

type family GetNewtypeConstructor (a :: Type) :: GetNewtypeInner a -> a where
  GetNewtypeConstructor a = DefineNewtypeConstructor a

coerceNewtypeDown :: a -> GetNewtypeInner a
coerceNewtypeDown = unsafeCoerce

coerceNewtypeUp :: GetNewtypeInner a -> a
coerceNewtypeUp = unsafeCoerce

-- SKI

infixr 0 ~>
data (~>) (a :: Type) (b :: Type) where
  S :: (a ~> b ~> c) ~> (a ~> b) ~> a ~> c
  K :: a ~> b ~> a
  I :: a ~> a
  (:@) :: ((a ~> b) ~> c ~> d) -> (a ~> b) -> c ~> d
  (:@@) :: (a ~> b ~> c) -> a -> b ~> c
  MkUnit :: a ~> ()
  MkPair :: a ~> b ~> (a, b)
  ElimPair :: (a, b) ~> (a ~> b ~> c) ~> c
  MkLeft :: a ~> Either a b
  MkRight :: b ~> Either a b
  ElimEither :: Either a b ~> (a ~> c) ~> (b ~> c) ~> c
  MkForall :: forall a f. (forall x. a ~> f x) -> a ~> ForallS f
  ElimForall :: ForallS f ~> f x
  MkSome :: forall f x. f x ~> Some f
  ElimSome :: forall a b c (f :: c -> Type). (a ~> Some f) -> (forall x. f x ~> b) -> a ~> b
  MkFix :: f (Fix f) ~> Fix f
  ElimFix :: Fix f ~> f (Fix f)
  MkNewtype' :: a :~: GetNewtypeInner b -> a ~> b
  ElimNewtype' :: GetNewtypeInner a :~: b -> a ~> b
data instance Single @(a ~> b) ski where
  SS :: Single 'S
  SK :: Single 'K
  SI :: Single 'I
  (:%@) :: Single x -> Single y -> Single (x ':@ y)
  (:%@@) :: Single x -> Single y -> Single (x ':@@ y)
  SMkUnit :: Single 'MkUnit
  SMkPair :: Single 'MkPair
  SElimPair :: Single 'ElimPair
  SMkLeft :: Single 'MkLeft
  SMkRight :: Single 'MkRight
  SElimEither :: Single 'ElimEither
  SMkForall ::
    forall a b f (y :: forall (x :: a). b ~> f x).
    Single @(forall (x :: a). b ~> f x) y -> Single ('MkForall y)
  SElimForall :: Single 'ElimForall
  SMkSome :: Single 'MkSome
  SElimSome ::
    forall a b c (f :: c -> Type) (x :: a ~> Some f) (y :: forall z. f z ~> b).
    Single x -> Single @(forall z. f z ~> b) y -> Single ('ElimSome x y)
  SMkFix :: Single 'MkFix
  SElimFix :: Single 'ElimFix
  SMkNewtype' :: Single eq -> Single ('MkNewtype' eq)
  SElimNewtype' :: Single eq -> Single ('ElimNewtype' eq)
instance Known K where known = SK
instance Known S where known = SS
instance Known I where known = SI
instance (Known x, Known y) => Known (x :@@ y) where known = known :%@@ known
instance (Known x, Known y) => Known (x :@ y) where known = known :%@ known
instance Known MkUnit where known = SMkUnit
instance Known MkPair where known = SMkPair
instance Known ElimPair where known = SElimPair
instance Known MkLeft where known = SMkLeft
instance Known MkRight where known = SMkRight
instance Known ElimEither where known = SElimEither
instance
  forall a b (f :: a -> Type) (t :: forall x. b ~> f x).
  (forall x. Known @(b ~> f x) t) => Known (MkForall t) where
    known = SMkForall (unsafeCoerce (known :: Single (t @Skolem)) :: Single @(forall x. b ~> f x) t)
instance Known ElimForall where known = SElimForall
instance Known MkSome where known = SMkSome
instance
  forall a b c (f :: c -> Type) (x :: a ~> Some f) (y :: forall z. f z ~> b).
  (Known x, (forall skolem. Known @(f skolem ~> b) (y @skolem))) => Known (ElimSome x y)
  where known = SElimSome known (unsafeCoerce (known :: Single (y @Skolem)))
instance Known MkFix where known = SMkFix
instance Known ElimFix where known = SElimFix
instance Known (MkNewtype' eq) where known = SMkNewtype' (error "FIXME")
instance Known (ElimNewtype' eq) where known = SElimNewtype' (error "FIXME")
instance Show (a ~> b) where
  showsPrec _ K = ('K' :)
  showsPrec _ S = ('S' :)
  showsPrec _ I = ('I' :)
  showsPrec prec (x :@@ _) | prec >= 10 =
    ('(' :) . showsPrec 10 x . (" <data>)" <>)
  showsPrec _ (x :@@ _) =
    showsPrec 10 x . (" <data>" <>)
  showsPrec prec (x :@ y) | prec >= 10 =
    ('(' :) . showsPrec 10 x . (' ' :) . showsPrec 10 y . (')' :)
  showsPrec _ (x :@ y) =
    showsPrec 10 x . (' ' :) . showsPrec 10 y
  showsPrec _ MkUnit = ("MkUnit" <>)
  showsPrec _ MkPair = ("MkPair" <>)
  showsPrec _ ElimPair = ("ElimPair" <>)
  showsPrec _ MkLeft = ("MkLeft" <>)
  showsPrec _ MkRight = ("MkRight" <>)
  showsPrec _ ElimEither = ("ElimEither" <>)
  showsPrec prec (MkForall t) | prec >= 10 = ("(MkForall " <>) . showsPrec 10 t . (')' :)
  showsPrec _ (MkForall t) = ("MkForall " <>) . showsPrec 10 t
  showsPrec _ ElimForall = ("ElimForall " <>)
  showsPrec _ MkSome = ("MkSome " <>)
  showsPrec prec (ElimSome x y) | prec >= 10 = ("(ElimSome " <>) . showsPrec 10 x . (' ' :) . showsPrec 10 y . (')' :)
  showsPrec _ (ElimSome x y) = ("ElimSome " <>) . showsPrec 10 x . (' ' :) . showsPrec 10 y
  showsPrec _ MkFix = ("MkFix" <>)
  showsPrec _ ElimFix = ("ElimFix" <>)
  showsPrec _ (MkNewtype' _) = ("MkNewtype" <>)
  showsPrec _ (ElimNewtype' _) = ("ElimNewtype" <>)

type family MkNewtype :: GetNewtypeInner b ~> b
type instance MkNewtype = 'MkNewtype' 'Refl

pattern MkNewtype :: GetNewtypeInner b ~> b
pattern MkNewtype = MkNewtype' Refl

type family ElimNewtype :: a ~> GetNewtypeInner a
type instance ElimNewtype = 'ElimNewtype' 'Refl

pattern ElimNewtype :: a ~> GetNewtypeInner a
pattern ElimNewtype = ElimNewtype' Refl

infixl 9 :@
infixl 9 :%@
infixl 9 :@@
infixl 9 :%@@

type family H3 (c :: a -> b) (x :: b) :: a where
  H3 c (c y) = y

type H4 :: forall a b (f :: a -> Type). Some f -> (forall x. f x ~> b) -> b
type family H4 (w :: Some f) (y :: forall x. f x ~> b) :: b where
  forall a b f (x :: a) (w :: f x) (y :: forall z. f z ~> b).
    H4 ('Some w) y = Interp y w

type Interp :: forall (a :: Type) (b :: Type). (a ~> b) -> a -> b
type family Interp (f :: a ~> b) (x :: a) :: b where
  Interp I x = x
  forall (a :: Type) (b :: Type) (x :: a).
    Interp @a @(b ~> a) ('K @a @b) x = 'K ':@@ x
  Interp (K :@@ x) _ = x
  Interp S x = S :@@ x
  Interp (S :@@ x) y = S :@@ x :@@ y
  Interp (S :@@ x :@@ y) z = Interp (Interp x z) (Interp y z)
  Interp MkUnit _ = '()
  Interp MkPair x = MkPair :@@ x
  Interp (MkPair :@@ x) y = '(x, y)
  Interp ElimPair x = ElimPair :@@ x
  Interp (ElimPair :@@ '(x, y)) f = f `Interp` x `Interp` y
  Interp MkLeft x = Left x
  Interp MkRight x = Right x
  Interp ElimEither x = ElimEither :@@ x
  Interp (ElimEither :@@ x) f = ElimEither :@@ x :@@ f
  Interp (ElimEither :@@ Left x :@@ f) _ = Interp f x
  Interp (ElimEither :@@ Right x :@@ _) g = Interp g x
  forall a b (f :: a -> Type) (t :: forall x. b ~> f x) (y :: b).
    Interp (MkForall t) y = 'ForallS t y
  forall a b (f :: a -> Type) (x :: forall z. b ~> f z) (y :: b).
    Interp ElimForall ('ForallS x y) = Interp x y
  Interp MkSome x = 'Some x
  forall a b c (f :: c -> Type) (x :: a ~> Some f) (y :: forall w. f w ~> b) (z :: a).
    Interp (ElimSome x y) z = H4 (Interp x z) y
  Interp MkFix x = 'Fix x
  Interp ElimFix ('Fix x) = x
  Interp (x :@@ y) z = Interp (Interp x y) z
  Interp (x :@ y) z = Interp (Interp x y) z
  Interp @a @b (MkNewtype' eq) x = GetNewtypeConstructor b (CoerceTo' eq x)
  Interp @a @b (ElimNewtype' eq) x = CoerceTo' eq (H3 (GetNewtypeConstructor a) x)

interp :: (a ~> b) -> a -> b
interp I x = x
interp K x = K :@@ x
interp (K :@@ x) _ = x
interp S x = S :@@ x
interp (S :@@ x) y = S :@@ x :@@ y
interp (S :@@ x :@@ y) z = (interp x z) `interp` (interp y z)
interp MkUnit _ = ()
interp MkPair x = MkPair :@@ x
interp (MkPair :@@ x) y = (x, y)
interp ElimPair x = ElimPair :@@ x
interp (ElimPair :@@ (x, y)) f = f `interp` x `interp` y
interp MkLeft x = Left x
interp MkRight x = Right x
interp ElimEither x = ElimEither :@@ x
interp (ElimEither :@@ x) f = ElimEither :@@ x :@@ f
interp (ElimEither :@@ Left x :@@ f) _ = interp f x
interp (ElimEither :@@ Right x :@@ _) g = interp g x
interp (MkForall x) y = ForallS x y
interp ElimForall (ForallS x y) = interp x y
interp MkSome x = Some x
interp (ElimSome x y) z = case interp x z of Some w -> interp y w
interp MkFix x = Fix x
interp ElimFix (Fix x) = x
interp (x :@@ y) z = interp (interp x y) z
interp (x :@ y) z = interp (interp x y) z
interp (MkNewtype' Refl) x = coerceNewtypeUp x
interp (ElimNewtype' Refl) x = coerceNewtypeDown x

-- Implementing this directly is *possible*, but you need some `unsafeCoerce` internally
-- on the `MkForall` and `ElimSome` cases, so it doesn't make much sense to do so.
sinterp :: Single (ski :: a ~> b) -> Single (x :: a) -> Single (Interp ski x :: b)
sinterp = unsafeCoerce interp

-- examples

type FlipS :: (a ~> b ~> c) ~> b ~> a ~> c
type FlipS = S :@ (S :@ (K :@ S) :@ (S :@ (K :@ K) :@ S)) :@ (K :@ K)

type ComposeS :: (b ~> c) ~> (a ~> b) ~> a ~> c
type ComposeS = S :@ (K :@ S) :@ K

type TwiceS :: a ~> (a ~> a ~> b) ~> b
type TwiceS = S :@ (S :@ (K :@ S) :@ (S :@ (K :@ (S :@ I)) :@ K)) :@ K

type TopairS :: a ~> (a, a)
type TopairS = FlipS :@ TwiceS :@ MkPair

newtype Id' a = Id' (a ~> a)

type instance DefineNewtypeInner (Id' a) = a ~> a
type instance DefineNewtypeConstructor (Id' a) = 'Id'

type IdS'' :: () ~> a ~> a
type IdS'' = K :@ I

type family IdS' :: forall a. () ~> Id' a
-- FIXME: GHC needs type-level big lambdas
--type instance IdS' = S :@ (K :@ MkNewtype) :@ (K :@ I)

type IdS :: () ~> ForallS Id'
type IdS = MkForall IdS'

idS :: () ~> ForallS Id'
idS = MkForall $ S :@ (K :@ MkNewtype) :@ (K :@ I)

type RemoveConstantS :: (c ~> a ~> b) ~> (a ~> c) ~> a ~> b
type RemoveConstantS = ComposeS :@ S :@ FlipS

type RemoveUnitS :: (() ~> a ~> b) ~> a ~> b
type RemoveUnitS = FlipS :@ RemoveConstantS :@ MkUnit

type IdS_recovered :: forall a. a ~> a
type IdS_recovered = RemoveUnitS :@ (ComposeS :@ ElimNewtype :@ (S :@ (K :@ ElimForall) :@ IdS))
