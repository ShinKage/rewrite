module Decidable.Extra

%default total
%access public export

||| Decision procedure for true booleans.
||| @b Boolean to check
decIsTrue : (b : Bool) -> Dec (b = True)
decIsTrue True = Yes Refl
decIsTrue False = No absurd

||| Decision procedure for false booleans.
||| @b Boolean to check
decIsFalse : (b : Bool) -> Dec (b = False)
decIsFalse False = Yes Refl
decIsFalse True = No absurd
