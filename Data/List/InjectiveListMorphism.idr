module Data.List.InjectiveListMorphism

import Data.List
import public Data.List.Morphism
import public Data.List.Pos
import Data.Maybe
import Decidable.Equality
import Syntax.PreorderReasoning

%default total

||| Tabulated injective function from a list of values to another list.
public export
data InjectiveListMorphism : List a -> List b -> Type where
  Nil : InjectiveListMorphism [] ys
  (::) : (i : Pos ys) -> InjectiveListMorphism xs (drop ys i) -> InjectiveListMorphism (x :: xs) ys

||| Check if an element of the image has a single preimage.
public export
dropCheck : (i : Pos ys) -> ListMorphism xs ys -> Maybe (ListMorphism xs (drop ys i))
dropCheck i [] = Just []
dropCheck i (x :: xs) with (dropCheck i xs)
  dropCheck i (x :: xs) | Just rest with (decEq x i)
    dropCheck i (i :: xs) | Just rest | Yes Refl = Nothing
    dropCheck i (x :: xs) | Just rest | No contra = Just (dropPos i x contra :: rest)
  dropCheck i (x :: xs) | Nothing = Nothing

||| Check if a given function is injective.
public export
isInjective : ListMorphism xs ys -> Maybe (InjectiveListMorphism xs ys)
isInjective [] = Just []
isInjective (i :: is) = [ i :: is' | is' <- isInjective =<< dropCheck i is ]

||| Type for tabulated injective functions from a list of values to another list.
||| Stores the function as a `ListMorphism` with a proof of injectivity, so that
||| manipulating the function is easier.
public export
record InjectiveMorphism {0 a, b : Type} (xs : List a) (ys : List b) where
  constructor MkInjective
  morphism : ListMorphism xs ys
  {auto 0 prf : IsJust (isInjective morphism)}

public export
injective : (f : ListMorphism xs ys) -> {auto 0 prf : IsJust (isInjective f)} -> InjectiveMorphism xs ys
injective f = MkInjective f {prf}

||| Returns the injective by construction version of an injective morphism.
public export
getInjective : InjectiveMorphism xs ys -> InjectiveListMorphism xs ys
getInjective (MkInjective f {prf}) with (isInjective f)
  getInjective (MkInjective f {prf = ItIsJust}) | Just f' = f'

||| Returns, if possible, the function with its injectivity proof.
public export
checkInjective : (f : ListMorphism xs ys) -> Maybe (InjectiveMorphism xs ys)
checkInjective f with (isItJust (isInjective f))
  checkInjective f | Yes prf = Just (MkInjective f)
  checkInjective f | No _ = Nothing

identityPrf : (xs : List a) -> IsJust (isInjective (identity xs))
identityPrf xs = believe_me (the (IsJust (Just Z)) ItIsJust)

||| Returns the identity function.
public export
identity : (xs : List a) -> InjectiveMorphism xs xs
identity xs = MkInjective (identity xs) {prf = identityPrf xs}

identityExtRightPrf : (xs, ys : List a) -> IsJust (isInjective (identityExtRight xs ys))
identityExtRightPrf xs ys = believe_me (the (IsJust (Just Z)) ItIsJust)

-- TODO: check if useful.
public export
identityExtRight : (xs, ys : List a) -> InjectiveMorphism xs (xs ++ ys)
identityExtRight xs ys = MkInjective (identityExtRight xs ys) {prf = identityExtRightPrf xs ys}

identityExtLeftPrf : (xs, ys : List a) -> IsJust (isInjective (identityExtLeft xs ys))
identityExtLeftPrf xs ys = believe_me (the (IsJust (Just Z)) ItIsJust)

-- TODO: check if useful.
public export
identityExtLeft : (xs, ys : List a) -> InjectiveMorphism ys (xs ++ ys)
identityExtLeft xs ys = MkInjective (identityExtLeft xs ys) {prf = identityExtLeftPrf xs ys}

rightShiftPrf : (f : ListMorphism xs ys) -> IsJust (isInjective (rightShift f))
rightShiftPrf f = believe_me (the (IsJust (Just Z)) ItIsJust)

||| Prepends a new element to the image of the injective function.
public export
rightShift : InjectiveMorphism xs ys -> InjectiveMorphism xs (y :: ys)
rightShift (MkInjective f) = MkInjective (rightShift f) {prf = rightShiftPrf f}

public export
rawRightShift : InjectiveListMorphism xs ys -> InjectiveListMorphism xs (y :: ys)
rawRightShift [] = []
rawRightShift (x :: xs) = There x :: rawRightShift xs

dropPrf : (f : ListMorphism xs ys) -> (i : Pos xs) -> IsJust (isInjective (drop f i))
dropPrf f i = believe_me (the (IsJust (Just Z)) ItIsJust)

||| Updates an injective function after removing an element from the domain.
public export
drop : InjectiveMorphism xs ys -> (i : Pos xs) -> InjectiveMorphism (drop xs i) ys
drop (MkInjective f) i = MkInjective (drop f i) {prf = dropPrf f i}

||| Applies the injective function at the specific domain value.
public export
apply : InjectiveMorphism xs ys -> Pos xs -> Pos ys
apply f x = apply f.morphism x

composePrf : (f : ListMorphism ys zs) -> (g : ListMorphism xs ys) -> IsJust (isInjective f) -> IsJust (isInjective g) -> IsJust (isInjective (compose f g))
composePrf f g prff prfg = believe_me (the (IsJust (Just Z)) ItIsJust)

||| Returns the composition of two injective functions.
public export
compose : InjectiveMorphism b c -> InjectiveMorphism a b -> InjectiveMorphism a c
compose (MkInjective f {prf = prff}) (MkInjective g {prf = prfg}) = MkInjective (compose f g) {prf = composePrf f g prff prfg}

||| Returns the composition of two injective functions.
public export
(.) : InjectiveMorphism b c -> InjectiveMorphism a b -> InjectiveMorphism a c
(.) = compose

public export
composeDistributive : (f : InjectiveMorphism ys zs) -> (g : InjectiveMorphism xs ys) -> f.morphism . g.morphism = (f . g).morphism
composeDistributive (MkInjective f) (MkInjective g) = Refl
