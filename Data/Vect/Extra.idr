module Data.Vect.Extra

import Data.Fin
import Data.Vect

%default total
%access public export

||| Checks if a vector of Maybes is full of values and returns the checked
||| vector or Nothing.
convertVect : Vect n (Maybe elem) -> Maybe (Vect n elem)
convertVect {n} xs with (catMaybes xs)
  convertVect {n} xs | (n' ** xs') with (decEq n n')
    convertVect {n} xs | (n  ** xs') | Yes Refl  = Just xs'
    convertVect {n} xs | (n' ** xs') | No contra = Nothing

invertFun : Vect n (Fin n) -> Vect n (Fin n)
invertFun xs = foldr (\i => replaceAt (index i xs) i) range range
