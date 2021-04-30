module Data.List.CList

import public Data.List.Pos

%default total

||| Type for lists that are in one-to-one correspondence to another list.
public export
data CList : List a -> Type -> Type where
  Nil : CList [] b
  (::) : (x : b) -> CList ys b -> CList (y :: ys) b

%name CList cs

public export
forget : CList xs b -> List b
forget [] = []
forget (x :: xs) = x :: forget xs

public export
Show b => Show (CList xs b) where
  show = show . forget

||| Initialize a one-to-one correspondence list with a default value.
public export
initialize : {xs : List a} -> b -> CList xs b
initialize {xs = []} x = []
initialize {xs = (_ :: xs)} x = x :: initialize {xs} x

||| Extracts an element from a one-to-one correspondence list by indexing the
||| corresponding element.
public export
index : CList xs b -> Pos xs -> b
index (x :: xs) Here = x
index (x :: xs) (There i) = index xs i

public export
Eq b => Eq (CList xs b) where
  [] == [] = True
  (x :: xs) == (y :: ys) = x == y && xs == ys

public export
Ord b => Ord (CList xs b) where
  compare [] [] = EQ
  compare (x :: xs) (y :: ys) = compare (x, xs) (y, ys)

public export
Functor (CList xs) where
  map f [] = []
  map f (x :: xs) = f x :: map f xs

public export
Foldable (CList xs) where
  foldr f s [] = s
  foldr f s (x :: xs) = f x (foldr f s xs)

  foldl f s [] = s
  foldl f s (x :: xs) = foldl f (f s x) xs

  null [] = True
  null (_ :: _) = False

public export
Traversable (CList xs) where
  traverse f [] = pure []
  traverse f (x :: xs) = [| f x :: traverse f xs |]

public export
Zippable (CList xs) where
  zipWith _ [] _ = []
  zipWith _ _ [] = []
  zipWith f (x :: xs) (y :: ys) = f x y :: zipWith f xs ys

  zipWith3 _ [] _ _ = []
  zipWith3 _ _ [] _ = []
  zipWith3 _ _ _ [] = []
  zipWith3 f (x :: xs) (y :: ys) (z :: zs) = f x y z :: zipWith3 f xs ys zs

  unzipWith f [] = ([], [])
  unzipWith f (x :: xs) = let (b, c) = f x
                              (bs, cs) = unzipWith f xs
                           in (b :: bs, c :: cs)

  unzipWith3 f [] = ([], [], [])
  unzipWith3 f (x :: xs) = let (b, c, d) = f x
                               (bs, cs, ds) = unzipWith3 f xs
                            in (b :: bs, c :: cs, d :: ds)


||| Replace an element from a one-to-one correspondence list by indexing the
||| corresponding element.
public export
replaceAt : CList xs b -> Pos xs -> b -> CList xs b
replaceAt (x :: xs) Here v = v :: xs
replaceAt (x :: xs) (There i) v = x :: replaceAt xs i v

public export
changePos : Pos xs -> (cs : CList xs b) -> Pos (forget cs)
changePos Here (c :: cs) = Here
changePos (There i) (c :: cs) = There (changePos i cs)
