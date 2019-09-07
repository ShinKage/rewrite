module Data.Fin.Extra

import Data.Fin

%default total
%access public export

Show (Fin n) where
  show = show . finToNat

||| Proof that some Fin is not the largest possible.
data FinNotLast : (n : Nat) -> Fin n -> Type where
  ||| Zero is not last if size is at least two
  ZNotLast : FinNotLast (S (S n)) FZ
  ||| If x is not last than it's successor is not last in a larger set
  SNotLast : FinNotLast n x -> FinNotLast (S n) (FS x)

||| Proof that x is less than or equal to y where x and y are both Fins of the
||| same size.
||| @x The smaller number
||| @y The larger number
data FinLTE : (x : Fin n) -> (y : Fin n) -> Type where
  ||| FZ is the smallest Fin
  LTEZero : FinLTE FZ y
  ||| If x <= y then x + 1 <= y + 1
  LTESucc : FinLTE x y -> FinLTE (FS x) (FS y)

Uninhabited (FinLTE (FS x) FZ) where
  uninhabited LTEZero     impossible
  uninhabited (LTESucc _) impossible

Uninhabited (FinNotLast 1 FZ) where
  uninhabited ZNotLast     impossible
  uninhabited (SNotLast _) impossible

||| A decision procedure for FinNotLast.
isNotLast : (x : Fin n) -> Dec (FinNotLast n x)
isNotLast {n = (S Z)}     FZ = No uninhabited
isNotLast {n = (S (S k))} FZ = Yes ZNotLast
isNotLast {n = (S (S k))} (FS x) with (isNotLast x)
  isNotLast {n = (S (S k))} (FS x) | Yes prf   = Yes (SNotLast prf)
  isNotLast {n = (S (S k))} (FS x) | No contra = No (\(SNotLast p) => contra p)

||| A decision procedure for FinLTE.
isFinLTE : (x : Fin n) -> (y : Fin n) -> Dec (FinLTE x y)
isFinLTE FZ     y  = Yes LTEZero
isFinLTE (FS x) FZ = No uninhabited
isFinLTE (FS x) (FS y) with (isFinLTE x y)
  isFinLTE (FS x) (FS y) | Yes prf   = Yes (LTESucc prf)
  isFinLTE (FS x) (FS y) | No contra = No (\(LTESucc p) => contra p)

||| Tightens the bound of non last Fin. A proof that the Fin is not the largest
||| possible is required.
||| @x The Fin to tighten
||| @prf A proof that x is not the largest possible
strengthen' : (x : Fin (S n)) -> (prf : FinNotLast (S n) x) -> Fin n
strengthen' {n = Z}     (FS FZ) (SNotLast _)   impossible
strengthen' {n = (S k)} FZ      ZNotLast       = FZ
strengthen' {n = (S k)} (FS x)  (SNotLast prf) = FS (strengthen' x prf)

||| x <= lim and x /= lim implies x is not last.
lteEqNotLast : (lim : Fin (S n)) -> (x : Fin (S n)) -> FinLTE x lim
            -> Not (lim = x) -> FinNotLast (S n) x
lteEqNotLast {n = Z}   FZ  FZ prf notEq = absurd $ notEq Refl
lteEqNotLast {n = S k} lim FZ prf notEq = ZNotLast
lteEqNotLast {n = S k} (FS lim) (FS x) (LTESucc prf) notEq
  = SNotLast (lteEqNotLast lim x prf (\Refl => notEq $ cong {f = FS} Refl))

||| Given a limit Fin and a proof that x /= lim, strengthens the bound of x if
||| x < lim otherwise decrements it by one.
||| @lim   The limit of the strengthen operation
||| @x     The Fin to strengthen
||| @notEq Proof that lim /= x
limitStrengthen : (lim : Fin (S n)) -> (x : Fin (S n))
               -> {auto notEq : Not (lim = x)} -> Fin n
limitStrengthen lim x {notEq} with (isFinLTE x lim)
  limitStrengthen lim x      {notEq} | Yes prf
    = strengthen' x (lteEqNotLast lim x prf notEq)
  limitStrengthen lim FZ     {notEq} | No contra = absurd $ contra LTEZero
  limitStrengthen lim (FS x) {notEq} | No contra = x
