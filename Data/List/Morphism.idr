module Data.List.Morphism

import Data.String
import Data.List
import public Data.List.Pos
import Decidable.Equality
import Syntax.PreorderReasoning

%default total

||| Tabulated function from a list of values to another list.
public export
data ListMorphism : List a -> List b -> Type where
  Nil : ListMorphism [] ys
  (::) : Pos ys -> ListMorphism xs ys -> ListMorphism (x :: xs) ys

||| Prepends a new element to the image of the function.
public export
rightShift : ListMorphism xs ys -> ListMorphism xs (y :: ys)
rightShift [] = []
rightShift (i :: is) = There i :: rightShift is

||| Identity function.
public export
identity : (xs : List a) -> ListMorphism xs xs
identity [] = []
identity (x :: xs) = Here :: rightShift (identity xs)

-- TODO: check if useful
public export
identityExtRight : (xs, ys : List a) -> ListMorphism xs (xs ++ ys)
identityExtRight [] ys = []
identityExtRight (x :: xs) ys = Here :: rightShift (identityExtRight xs ys)

-- TODO: check if useful
public export
identityExtLeft : (xs, ys : List a) -> ListMorphism ys (xs ++ ys)
identityExtLeft [] ys = identity ys
identityExtLeft (x :: xs) ys = rightShift (identityExtLeft xs ys)

||| Applies the function at the specific domain value.
public export
apply : ListMorphism xs ys -> Pos xs -> Pos ys
apply (f :: fs) Here = f
apply (_ :: fs) (There x) = apply fs x

||| Returns the composition of two functions.
public export
compose : ListMorphism b c -> ListMorphism a b -> ListMorphism a c
compose f [] = []
compose f (g :: gs) = apply f g :: compose f gs

||| Returns the composition of two functions.
public export
(.) : ListMorphism b c -> ListMorphism a b -> ListMorphism a c
(.) = compose

||| Updates a function after removing an element from the domain.
public export
drop : ListMorphism xs ys -> (i : Pos xs) -> ListMorphism (drop xs i) ys
drop (x :: xs) Here = xs
drop (x :: xs) (There i) = x :: drop xs i

public export
mapDomainList : ListMorphism xs ys -> ListMorphism (map f xs) ys
mapDomainList [] = []
mapDomainList (x :: xs) = x :: mapDomainList xs

public export
mapImageList : ListMorphism xs ys -> ListMorphism xs (map f ys)
mapImageList [] = []
mapImageList (x :: xs) = mapList x :: mapImageList xs

public export
mapList : ListMorphism xs ys -> ListMorphism (map f xs) (map f ys)
mapList [] = []
mapList (x :: xs) = mapList x :: mapList xs

||| Returns the list of preimages for a given image.
public export
preimages : Pos ys -> ListMorphism xs ys -> List (Pos xs)
preimages i [] = []
preimages i (x :: xs) with (decEq x i)
  preimages x (x :: xs) | Yes Refl = Here :: map There (preimages x xs)
  preimages i (x :: xs) | No contra = map There (preimages i xs)

||| Returns the image of a function.
public export
extract : (ys : List b) -> (f : ListMorphism xs ys) -> List b
extract ys [] = []
extract ys (i :: is) = index ys i :: extract ys is

-- TODO: check if useful
public export
append : (xs, ys : List a) -> (ws, zs : List b) -> ListMorphism xs ws -> ListMorphism ys zs -> ListMorphism (xs ++ ys) (ws ++ zs)
append [] [] ws zs [] [] = []
append [] (y :: ys) ws zs [] (g :: gs) = weakenLeft g :: append [] ys ws zs [] gs
append (x :: xs) ys ws zs (f :: fs) g = weakenRight f :: append xs ys ws zs fs g

public export
forget : ListMorphism xs ys -> List (Pos ys)
forget [] = []
forget (x :: xs) = x :: forget xs

public export
Show (ListMorphism xs ys) where
  show = show . forget

public export
Uninhabited (ListMorphism (x :: xs) []) where
  uninhabited (Here :: _) impossible
  uninhabited (There i :: _) impossible

public export
DecEq (ListMorphism xs ys) where
  decEq [] [] = Yes Refl
  decEq (i :: is) (j :: js) with (decEq i j)
    decEq (i :: is) (i :: js) | Yes Refl with (decEq is js)
      decEq (i :: is) (i :: is) | Yes Refl | Yes Refl = Yes Refl
      decEq (i :: is) (i :: js) | Yes Refl | No contra = No (\case Refl => contra Refl)
    decEq (i :: is) (j :: js) | No contra = No (\case Refl => contra Refl)

public export
consInjective1 : (0 _ : ListMorphism (x :: xs) ys = ListMorphism (z :: zs) ws) -> x = z
consInjective1 Refl = Refl

public export
consInjective2 : (0 _ : ListMorphism (x :: xs) ys = ListMorphism (z :: zs) ws) -> xs = zs
consInjective2 Refl = Refl

public export
applyComposeLemma : (f : ListMorphism b c) -> (g : ListMorphism a b) -> (x : Pos a)
                 -> apply (f . g) x = apply f (apply g x)
applyComposeLemma f (g :: gs) Here = Refl
applyComposeLemma f (g :: gs) (There i) = applyComposeLemma f gs i

public export
applyRightShift : {0 ys : List b} -> {0 y : b} -> (f : ListMorphism xs ys) -> (i : Pos xs)
               -> apply (rightShift {y} f) i = There (apply f i)
applyRightShift (x :: xs) Here = Refl
applyRightShift (x :: xs) (There i) = applyRightShift xs i

public export
applyIdentityUnit : (xs : List a) -> (i : Pos xs) -> apply (identity xs) i = i
applyIdentityUnit (x :: xs) Here = Refl
applyIdentityUnit (x :: xs) (There i) = Calc $
  |~ apply (identity (x :: xs)) (There i)
  ~~ apply (rightShift (identity xs)) i   ...(Refl)
  ~~ There (apply (identity xs) i)        ...(applyRightShift (identity xs) i)
  ~~ There i                              ...(cong There (applyIdentityUnit xs i))

public export
composeLeftUnit : (f : ListMorphism xs ys) -> (identity ys) . f = f
composeLeftUnit [] = Refl
composeLeftUnit (f :: fs) = Calc $
  |~ apply (identity ys) f :: (identity ys) . fs
  ~~ apply (identity ys) f :: fs                 ...(cong (apply (identity ys) f ::) (composeLeftUnit fs))
  ~~ f :: fs                                     ...(cong (:: fs) (applyIdentityUnit ys f))

public export
composeRightUnitLemma : {xs : List a} -> (f : Pos ys) -> (fs : ListMorphism xs ys) -> (i : Pos xs)
                     -> apply ((f :: fs) . (rightShift (identity xs))) i = apply (fs . (identity xs)) i
composeRightUnitLemma {xs = x :: xs} f fs i = Calc $
  |~ apply ((f :: fs) . (rightShift (identity (x :: xs)))) i
  ~~ apply (f :: fs) (apply (rightShift (identity (x :: xs))) i) ...(applyComposeLemma (f :: fs) (rightShift (identity (x :: xs))) i)
  ~~ apply (f :: fs) (There {x} (apply (identity (x :: xs)) i))  ...(cong (apply (f :: fs)) $ applyRightShift (identity (x :: xs)) i)
  ~~ apply fs (apply (identity (x :: xs)) i)                     ...(Refl)
  ~~ apply (fs . (identity (x :: xs))) i                         ...(sym $ applyComposeLemma fs (identity (x :: xs)) i)

public export
extensionality : (f, g : ListMorphism xs ys) -> ((i : Pos xs) -> apply f i = apply g i) -> f = g
extensionality [] [] prf = Refl
extensionality (f :: fs) (g :: gs) prf = Calc $
  |~ f :: fs
  ~~ g :: fs ...(cong (:: fs) (prf Here))
  ~~ g :: gs ...(cong (g ::) (extensionality fs gs (\i => prf (There i))))

public export
composeRightUnit : {xs : List _} -> (f : ListMorphism xs ys) -> f . (identity xs) = f
composeRightUnit [] = Refl
composeRightUnit {xs = x :: xs} (f :: fs) = Calc $
  |~ (f :: fs) . (identity (x :: xs))
  ~~ f :: (f :: fs) . (rightShift (identity xs)) ...(Refl)
  ~~ f :: fs . (identity xs)                     ...(cong (f ::) (extensionality _ _ $ composeRightUnitLemma f fs))
  ~~ f :: fs                                     ...(cong (f ::) $ composeRightUnit fs)

public export
composeAssociative : (f : ListMorphism ws zs) -> (g : ListMorphism ys ws) -> (h : ListMorphism xs ys)
                  -> f . (g . h) = (f . g) . h
composeAssociative f g [] = Refl
composeAssociative f [] (_ :: _) impossible
composeAssociative [] (_ :: _) (_ :: _) impossible
composeAssociative (f :: fs) (g :: gs) (h :: hs) = case h of
  Here => rewrite composeAssociative (f :: fs) (g :: gs) hs in Refl
  There h => rewrite composeAssociative (f :: fs) (g :: gs) hs in
             rewrite applyComposeLemma (f :: fs) gs h in Refl

public export
dropLemma : (f : ListMorphism ys zs) -> (g : ListMorphism xs ys) -> (i : Pos xs) -> f . (drop g i) = drop (f . g) i
dropLemma [] (Here :: _) _ impossible
dropLemma [] (There j :: _) _ impossible
dropLemma (f :: fs) (g :: gs) Here = Refl
dropLemma (f :: fs) (g :: gs) (There i) = cong (apply (f :: fs) g ::) (dropLemma (f :: fs) gs i)

public export
shiftLemma : {0 xs : List a} -> {0 y : b} -> {0 ys : List b} -> {0 zs : List c}
          -> (f : Pos zs) -> (fs : ListMorphism ys zs) -> (g : ListMorphism xs ys)
          -> (f :: fs) . (rightShift {y} g) = fs . g
shiftLemma f fs [] = Refl
shiftLemma f fs (g :: gs) = cong (apply fs g ::) (shiftLemma f fs gs)

public export
shiftDropDistributivity : {0 y : _} -> (f : ListMorphism xs ys) -> (i : Pos xs)
                       -> drop (rightShift {y} f) i = rightShift {y} (drop f i)
shiftDropDistributivity (f :: fs) Here = Refl
shiftDropDistributivity (f :: fs) (There i) = cong (There f ::) (shiftDropDistributivity fs i)

public export
shiftIdentityLemma : {0 y : _} -> (ys : List b) -> (f : ListMorphism xs ys)
                  -> rightShift {y} (identity ys) . f = rightShift {y} f
shiftIdentityLemma ys [] = Refl
shiftIdentityLemma ys (f :: fs) = Calc $
  |~ apply (rightShift {y} (identity ys)) f :: (rightShift {y} (identity ys)) . fs
  ~~ apply (rightShift {y} (identity ys)) f :: rightShift {y} fs
       ...(cong (apply (rightShift {y} (identity ys)) f ::) (shiftIdentityLemma ys fs))
  ~~ There (apply (identity ys) f) :: rightShift {y} fs
       ...(cong (:: rightShift {y} fs) (applyRightShift {y} (identity ys) f))
  ~~ There f :: rightShift {y} fs
       ...(cong (\x => There x :: rightShift {y} fs) (applyIdentityUnit ys f))

||| Proof that identity behaves the same after removing an element from the domain.
public export
applyIdentityDropLemma : (xs : List a) -> (i : Pos xs) -> (s : Pos xs) -> (contra : Not (s = i))
                      -> s = apply (drop (identity xs) i) (dropPos i s contra)
applyIdentityDropLemma (x :: xs) Here Here contra = absurd (contra Refl)
applyIdentityDropLemma (x :: xs) (There i) Here contra = Refl
applyIdentityDropLemma (x :: xs) Here (There j) contra = Calc $
  |~ There j
  ~~ There (apply (identity xs) j)              ...(cong There (sym $ applyIdentityUnit xs j))
  ~~ apply (rightShift {y = x} (identity xs)) j ...(sym $ applyRightShift {y = x} (identity xs) j)
applyIdentityDropLemma (x :: xs) (There i) (There j) contra with (decEq i j)
  applyIdentityDropLemma (x :: xs) (There i) (There i) contra | Yes Refl = absurd (contra Refl)
  applyIdentityDropLemma (x :: xs) (There i) (There j) contra | No f = Calc $
    |~ There j
    ~~ There (apply (drop (identity xs) i) (dropPos i j (notThereInjective contra)))
         ...(cong There (applyIdentityDropLemma xs i j (notThereInjective contra)))
    ~~ apply (rightShift {y = x} (drop (identity xs) i)) (dropPos i j (notThereInjective contra))
         ...(sym $ applyRightShift {y = x} (drop (identity xs) i) (dropPos i j (notThereInjective contra)))
    ~~ apply (drop (rightShift {y = x} (identity xs)) i) (dropPos i j (notThereInjective contra))
         ...(cong (\x => apply x (dropPos i j (notThereInjective contra))) (sym $ shiftDropDistributivity {y = x} (identity xs) i))

public export
showMorphism : (Show a, Show b) => {xs : List a} -> {ys : List b} -> ListMorphism xs ys -> String
showMorphism = unlines . go
  where
    go : {zs : List a} -> {ws : List b} -> ListMorphism zs ws -> List String
    go [] = []
    go {zs = z :: zs} (p :: ps) = "\{show z} -> \{show $ index ws p}" :: go ps
