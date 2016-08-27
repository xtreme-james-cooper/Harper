module Harper.Agda.Cha15Type where

open import AgdaUtils.Basics
open import AgdaUtils.Nat
open import AgdaUtils.Fin
open import AgdaUtils.Vect
open import AgdaUtils.SetsB

data type (tn : nat) : Set where
  TyVar : (x : fin tn) -> type tn
  Nat : type tn
  Arr : (t1 t2 : type tn) -> type tn
  Prod : {n : nat} (ts : vect (type tn) n) -> type tn
  Sum : {n : nat} (ts : vect (type tn) n) -> type tn

tfreevars : {tn : nat} -> type tn -> set (fin tn)
tfreevarsVect : {tn n : nat} -> vect (type tn) n -> set (fin tn)
tfreevars (TyVar x)   = Insert x Empty
tfreevars Nat         = Empty
tfreevars (Arr t1 t2) = tfreevars t1 ∪ tfreevars t2
tfreevars (Prod ts)   = tfreevarsVect ts
tfreevars (Sum ts)    = tfreevarsVect ts
tfreevarsVect []        = Empty
tfreevarsVect (t :: ts) = tfreevars t ∪ tfreevarsVect ts 

tsubst : {tn : nat} -> type tn -> fin (Suc tn) -> type (Suc tn) -> type tn
tsubstVect : {tn m : nat} -> type tn -> fin (Suc tn) -> vect (type (Suc tn)) m -> vect (type tn) m
tsubst t' x (TyVar y)   with finEq y x
tsubst t' x (TyVar .x)  | Yes Refl = t'
tsubst t' x (TyVar y)   | No neq   = TyVar (fdecr x y neq)
tsubst t' x Nat         = Nat
tsubst t' x (Arr t1 t2) = Arr (tsubst t' x t1) (tsubst t' x t2)
tsubst t' x (Prod ts)   = Prod (tsubstVect t' x ts)
tsubst t' x (Sum ts)    = Sum (tsubstVect t' x ts)
tsubstVect t' x []        = []
tsubstVect t' x (t :: ts) = tsubst t' x t :: tsubstVect t' x ts

tsubstVectLookup : {n tn : nat} (t' : type tn) (ts : vect (type (Suc tn)) n) (x : fin (Suc tn)) (y : fin n) -> tsubstVect t' x ts ! y == tsubst t' x (ts ! y)
tsubstVectLookup t' []        x ()
tsubstVectLookup t' (t :: ts) x FZ     = Refl
tsubstVectLookup t' (t :: ts) x (FS y) = tsubstVectLookup t' ts x y

tsubstNmemEq : {tn : nat} {x : fin (Suc tn)} (t1 t2 : type tn) (t : type (Suc tn)) -> not (x ∈ tfreevars t) -> tsubst t1 x t == tsubst t2 x t
tsubstNmemEqVect : {tn m : nat} {x : fin (Suc tn)} (t1 t2 : type tn) (ts : vect (type (Suc tn)) m) -> not (x ∈ tfreevarsVect ts) -> tsubstVect t1 x ts == tsubstVect t2 x ts
tsubstNmemEq {x = x} t1 t2 (TyVar y)     nmem with finEq y x 
tsubstNmemEq {x = x} t1 t2 (TyVar .x)    nmem | Yes Refl with nmem Here
tsubstNmemEq {x = x} t1 t2 (TyVar .x)    nmem | Yes Refl | ()
tsubstNmemEq {x = x} t1 t2 (TyVar y)     nmem | No neq   = Refl
tsubstNmemEq {x = x} t1 t2 Nat           nmem = Refl
tsubstNmemEq {x = x} t1 t2 (Arr tt1 tt2) nmem 
  rewrite tsubstNmemEq t1 t2 tt1 (nmemUnionFst x (tfreevars tt1) (tfreevars tt2) nmem)
        | tsubstNmemEq t1 t2 tt2 (nmemUnionSnd x (tfreevars tt1) (tfreevars tt2) nmem) = Refl
tsubstNmemEq {x = x} t1 t2 (Prod ts)     nmem rewrite tsubstNmemEqVect t1 t2 ts nmem = Refl
tsubstNmemEq {x = x} t1 t2 (Sum ts)      nmem rewrite tsubstNmemEqVect t1 t2 ts nmem = Refl
tsubstNmemEqVect {x = x} t1 t2 []        nmem = Refl
tsubstNmemEqVect {x = x} t1 t2 (t :: ts) nmem 
  rewrite tsubstNmemEq t1 t2 t (nmemUnionFst x (tfreevars t) (tfreevarsVect ts) nmem) 
        | tsubstNmemEqVect t1 t2 ts (nmemUnionSnd x (tfreevars t) (tfreevarsVect ts) nmem) = Refl

data polytype {tn : nat} (x : fin tn) : type tn -> Set where
  PolyVar : polytype x (TyVar x)
  PolyNat : polytype x Nat
  PolyProd : {n : nat} {ts : vect (type tn) n} -> all (polytype x) ts -> polytype x (Prod ts)
  PolySum : {n : nat} {ts : vect (type tn) n} -> all (polytype x) ts -> polytype x (Sum ts)
  PolyArr : (t1 t2 : type tn) -> not (x ∈ tfreevars t1) -> polytype x t2 -> polytype x (Arr t1 t2)

