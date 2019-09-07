module Data.Vect.Subset

import Data.Vect

%default total
%access public export

||| Type parameterized by a vector. For each element of the vector, marks the
||| element whether is in or out the subset.
data VSub : Vect n a -> Type where
  Empty : VSub []
  In    : VSub xs -> VSub (x :: xs)
  Out   : VSub xs -> VSub (x :: xs)

%name VSub sub, sub1, sub2

Eq (VSub xs) where
  (==) Empty      Empty      = True
  (==) (In sub1)  (In sub2)  = sub1 == sub2
  (==) (Out sub1) (Out sub2) = sub1 == sub2
  (==) _ _ = False

||| Returns the size of the part marked as `In`.
size : VSub xs -> Nat
size Empty     = 0
size (In sub)  = 1 + size sub
size (Out sub) = size sub

||| Proof that the size of the subset is less than or equal to the
||| size of the vector.
||| @xs  The vector
||| @sub The subset
sizeLTE : (xs : Vect n a) -> (sub : VSub xs) -> LTE (size sub) n
sizeLTE [] Empty            = LTEZero
sizeLTE (x :: xs) (In sub)  = LTESucc (sizeLTE xs sub)
sizeLTE (x :: xs) (Out sub) = lteSuccRight $ sizeLTE xs sub

||| Extracts the subset from the vector.
extract : (xs : Vect n a) -> (sub : VSub xs) -> Vect (size sub) a
extract [] Empty            = []
extract (x :: xs) (In sub)  = x :: extract xs sub
extract (x :: xs) (Out sub) = extract xs sub

||| Returns the empty subset.
none : {xs : Vect n a} -> VSub xs
none {xs = []}        = Empty
none {xs = (_ :: xs)} = Out none

||| Add the given element to the subset.
add : {xs : Vect n a} -> Fin n -> VSub xs -> VSub xs
add FZ     (In sub)  = In sub
add FZ     (Out sub) = In sub
add (FS x) (In sub)  = In (add x sub)
add (FS x) (Out sub) = Out (add x sub)

||| Appends a new element to the vector head and depending on the boolean
||| arguments, adds it to the subset.
||| @b   True if the element needs to be added to the subset, False otherwise
||| @sub The subset
insert : (b : Bool) -> (sub : VSub xs) -> VSub (x :: xs)
insert False sub = Out sub
insert True  sub = In sub

||| Removes the given element from the subset.
remove : {xs : Vect n a} -> Fin n -> VSub xs -> VSub xs
remove FZ     (In sub)  = Out sub
remove FZ     (Out sub) = Out sub
remove (FS x) (In sub)  = In (remove x sub)
remove (FS x) (Out sub) = Out (remove x sub)

||| Removes the element at the given index from the vector and the subset.
delete : {xs : Vect (S n) a} -> (i : Fin (S n)) -> VSub xs
      -> VSub (deleteAt i xs)
delete           FZ     (In sub)  = sub
delete           FZ     (Out sub) = sub
delete {n = S k} (FS x) (In sub)  = In (delete x sub)
delete {n = S k} (FS x) (Out sub) = Out (delete x sub)

||| Returns True if the element at the given index is in the subset,
||| False otherwise.
contains : {xs : Vect n a} -> Fin n -> VSub xs -> Bool
contains FZ     (In sub)  = True
contains FZ     (Out sub) = False
contains (FS x) (In sub)  = contains x sub
contains (FS x) (Out sub) = contains x sub

||| Returns the union of two subset on the same vector.
union : VSub xs -> VSub xs -> VSub xs
union Empty      Empty      = Empty
union (In sub1)  (In sub2)  = In (union sub1 sub2)
union (In sub1)  (Out sub2) = In (union sub1 sub2)
union (Out sub1) (In sub2)  = In (union sub1 sub2)
union (Out sub1) (Out sub2) = Out (union sub1 sub2)

||| Returns the intersection of two subset on the same vector.
intersect : VSub xs -> VSub xs -> VSub xs
intersect Empty      Empty      = Empty
intersect (In sub1)  (In sub2)  = In (intersect sub1 sub2)
intersect (In sub1)  (Out sub2) = Out (intersect sub1 sub2)
intersect (Out sub1) (In sub2)  = Out (intersect sub1 sub2)
intersect (Out sub1) (Out sub2) = Out (intersect sub1 sub2)

||| Returns the subtraction of two subset on the same vector.
subtract : VSub xs -> VSub xs -> VSub xs
subtract Empty      Empty      = Empty
subtract (In sub1)  (In sub2)  = Out (subtract sub1 sub2)
subtract (In sub1)  (Out sub2) = In (subtract sub1 sub2)
subtract (Out sub1) (In sub2)  = Out (subtract sub1 sub2)
subtract (Out sub1) (Out sub2) = Out (subtract sub1 sub2)

||| Builds a subset from a list of indices.
fromFins : {xs : Vect n a} -> List (Fin n) -> VSub xs
fromFins = foldl (flip add) none

||| Returns the vector of the indices of the element in the subset.
toFins : {xs : Vect n a} -> (sub : VSub xs) -> Vect (size sub) (Fin n)
toFins Empty     = []
toFins (In sub)  = FZ :: map FS (toFins sub)
toFins (Out sub) = map FS (toFins sub)

||| Maps a subset from a vector to another vector of the same length.
||| @xs  The vector associated to the subset
||| @ys  The new vector of the same length
||| @sub The subset
sameLength : (xs : Vect n a) -> (ys : Vect n b) -> (sub : VSub xs) -> VSub ys
sameLength []        []        Empty     = Empty
sameLength (x :: xs) (y :: ys) (In sub)  = In (sameLength xs ys sub)
sameLength (x :: xs) (y :: ys) (Out sub) = Out (sameLength xs ys sub)

||| Returns the complementary of a subset.
invert : VSub xs -> VSub xs
invert Empty     = Empty
invert (In sub)  = Out (invert sub)
invert (Out sub) = In (invert sub)
