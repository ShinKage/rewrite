module Data.List.Pos

import public Data.Maybe
import public Data.List
import Decidable.Equality

%default total

||| Type of bound-safe indices for lists.
public export
data Pos : List a -> Type where
  Here : Pos (x :: xs)
  There : Pos xs -> Pos (x :: xs)

%name Pos i, j, k

public export
Uninhabited (Pos []) where
  uninhabited Here impossible
  uninhabited (There _) impossible

public export
Uninhabited (Here = There {x} p) where
  uninhabited Refl impossible

public export
Uninhabited (There {x} p = Here) where
  uninhabited Refl impossible

public export
Eq (Pos xs) where
  Here == Here = True
  (There i) == (There j) = i == j
  _ == _ = False

public export
Ord (Pos xs) where
  compare Here Here = EQ
  compare Here (There i) = LT
  compare (There i) Here = GT
  compare (There i) (There j) = compare i j

public export
DecEq (Pos xs) where
  decEq Here Here = Yes Refl
  decEq Here (There x) = No uninhabited
  decEq (There x) Here = No uninhabited
  decEq (There x) (There y) with (decEq x y)
    decEq (There x) (There x) | Yes Refl = Yes Refl
    decEq (There x) (There y) | No contra = No (\case Refl => contra Refl)

public export
thereInjective : There i = There j -> i = j
thereInjective Refl = Refl

public export
notThereInjective : Not (There i = There j) -> Not (i = j)
notThereInjective f Refl = f Refl

||| Extracts a specific element from a list.
public export
index : (xs : List a) -> Pos xs -> a
index (x :: xs) Here = x
index (x :: xs) (There i) = index xs i

||| Removes a specific element from a list.
public export
drop : (xs : List a) -> Pos xs -> List a
drop (x :: xs) Here = xs
drop (x :: xs) (There i) = x :: drop xs i

||| Updates the bound-safe index of a list after removing another element from the list.
||| @i The index of the removed element
||| @j The index to update
||| @contra Proof that the two indices are not the same
public export
dropPos : (i : Pos xs) -> (j : Pos xs) -> (contra : j = i -> Void) -> Pos (drop xs i)
dropPos Here Here contra = absurd (contra Refl)
dropPos Here (There j) contra = j
dropPos (There i) Here contra = Here
dropPos (There i) (There j) contra with (decEq i j)
  dropPos (There i) (There i) contra | Yes Refl = absurd (contra Refl)
  dropPos (There i) (There j) contra | No _ = There (dropPos i j (notThereInjective contra))

||| Updates the bound-safe index of a list after adding another element to the list.
||| @i The index of the inserted element
||| @j The index to update
public export
shiftPos : (i : Pos ys) -> (j : Pos (drop ys i)) -> Pos ys
shiftPos Here j = There j
shiftPos (There i) Here = Here
shiftPos (There i) (There j) = There (shiftPos i j)

||| Updates the bound-safe index of a list after prepending another list.
public export
weakenLeft : {xs : List a} -> (i : Pos ys) -> Pos (xs ++ ys)
weakenLeft {xs = []} i = i
weakenLeft {xs = (x :: xs)} i = There (weakenLeft i)

||| Updates the bound-safe index of a list after appending another list.
public export
weakenRight : (i : Pos xs) -> Pos (xs ++ ys)
weakenRight Here = Here
weakenRight (There i) = There (weakenRight i)

||| Replace the element in the list at the given position.
public export
replaceAt : (xs : List a) -> Pos xs -> a -> List a
replaceAt (x :: xs) Here v = v :: xs
replaceAt (x :: xs) (There i) v = x :: replaceAt xs i v

||| Returns the list of bound-safe indices for a given list.
public export
range : (xs : List a) -> List (Pos xs)
range [] = []
range (x :: xs) = Here :: map There (range xs)

public export
mapList : Pos xs -> Pos (map f xs)
mapList Here = Here
mapList (There i) = There (mapList i)

public export
natToPos : {xs : List a} -> Nat -> Maybe (Pos xs)
natToPos {xs = []} k = Nothing
natToPos {xs = _ :: _} Z = Just Here
natToPos {xs = _ :: _} (S k) = There <$> natToPos k

public export
posToNat : Pos xs -> Nat
posToNat Here = Z
posToNat (There i) = S (posToNat i)

public export
integerToPos : {xs : List a} -> Integer -> Maybe (Pos xs)
integerToPos {xs = []} x = Nothing
integerToPos {xs = (_ :: _)} x = if x >= 0 then natToPos (fromInteger x) else Nothing

public export
fromInteger : {xs : List a} -> (x : Integer) -> IsJust (integerToPos {xs} x) => Pos xs
fromInteger {xs} x @{prf} with (integerToPos {xs} x)
  fromInteger {xs = xs} x @{ItIsJust} | Just i = i

public export
Show (Pos xs) where
  show = show . posToNat
