module Decidable.Extra

%default total

||| Decision procedure for true booleans.
||| @b Boolean to check
public export
decIsTrue : (b : Bool) -> Dec (b = True)
decIsTrue True = Yes Refl
decIsTrue False = No absurd

||| Decision procedure for false booleans.
||| @b Boolean to check
public export
decIsFalse : (b : Bool) -> Dec (b = False)
decIsFalse False = Yes Refl
decIsFalse True = No absurd
