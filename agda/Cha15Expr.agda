module Harper.Agda.Cha15Expr where

open import AgdaUtils.Basics
open import AgdaUtils.Nat
open import AgdaUtils.Fin
open import AgdaUtils.Vect
open import Harper.Agda.Cha15Type

data expr {n tn : nat} (Γ : vect (type tn) n) : type tn -> Set
data tuple {n tn : nat} (Γ : vect (type tn) n) : {m : nat} -> vect (type tn) m -> Set
data patn {n tn : nat} (Γ : vect (type tn) n) : {m : nat} -> vect (type tn) m -> type tn -> Set
data expr {n} {tn} Γ where
  Var : {t : type tn} (x : fin n) (pf : Γ ! x == t) -> expr Γ t
  Zero : expr Γ Nat
  Suc : (e : expr Γ Nat) -> expr Γ Nat
  Rec : {t : type tn} (e : expr Γ Nat) (eO : expr Γ t) (eS : expr (Nat :: t :: Γ) t) -> expr Γ t
  Lam : {t1 t2 : type tn} (e : expr (t1 :: Γ) t2) -> expr Γ (Arr t1 t2)
  App : {t1 t2 : type tn} (e1 : expr Γ (Arr t1 t2)) (e2 : expr Γ t1) -> expr Γ t2
  Tuple : {m : nat} {ts : vect (type tn) m} (es : tuple Γ ts) -> expr Γ (Prod ts)
  Proj : {m : nat} {ts : vect (type tn) m} (x : fin m) (e : expr Γ (Prod ts)) -> expr Γ (ts ! x)  
  Inj : {m : nat} (ts : vect (type tn) m) (x : fin m) (e : expr Γ (ts ! x)) -> expr Γ (Sum ts)
  Match : {t : type tn} {m : nat} {ts : vect (type tn) m} (e : expr Γ (Sum ts)) (es : patn Γ ts t) -> expr Γ t
  Map : {t1 t2 : type tn} {t : type (Suc tn)} (e' : expr (t1 :: Γ) t2) (e : expr Γ (tsubst t1 FZ t)) (pf : polytype FZ t) -> expr Γ (tsubst t2 FZ t)
data tuple {n} {tn} Γ where
  Unit : tuple Γ []
  Pair : {t : type tn} {m : nat} {ts : vect (type tn) m} (e : expr Γ t) (es : tuple Γ ts) -> tuple Γ (t :: ts)
data patn {n} {tn} Γ where
  Abort : {t : type tn} -> patn Γ [] t
  Case : {t t' : type tn} {m : nat} {ts : vect (type tn) m} (e : expr (t' :: Γ) t) (es : patn Γ ts t) -> patn Γ (t' :: ts) t

incr : {n tn : nat} {Γ : vect (type tn) n} {t t' : type tn} (x : fin (Suc n)) -> expr Γ t -> expr (insertAt x Γ t') t
incrTuple : {n tn m : nat} {Γ : vect (type tn) n} {ts : vect (type tn) m} {t' : type tn} (x : fin (Suc n)) -> tuple Γ ts -> tuple (insertAt x Γ t') ts
incrPatn : {n tn m : nat} {Γ : vect (type tn) n} {t t' : type tn} {ts : vect (type tn) m} (x : fin (Suc n)) -> patn Γ ts t -> patn (insertAt x Γ t') ts t
incr {Γ = Γ} {t' = t'} x (Var y Refl)  = Var (fincr x y) (insertAtFincr Γ y x t')
incr {Γ = Γ} {t' = t'} x Zero          = Zero
incr {Γ = Γ} {t' = t'} x (Suc e)       = Suc (incr x e)
incr {Γ = Γ} {t' = t'} x (Rec e eO eS) = Rec (incr x e) (incr x eO) (incr (FS (FS x)) eS)
incr {Γ = Γ} {t' = t'} x (Lam e)       = Lam (incr (FS x) e)
incr {Γ = Γ} {t' = t'} x (App e1 e2)   = App (incr x e1) (incr x e2)
incr {Γ = Γ} {t' = t'} x (Tuple es)    = Tuple (incrTuple x es)
incr {Γ = Γ} {t' = t'} x (Proj y e)    = Proj y (incr x e)
incr {Γ = Γ} {t' = t'} x (Inj ts y e)  = Inj ts y (incr x e)
incr {Γ = Γ} {t' = t'} x (Match e es)  = Match (incr x e) (incrPatn x es)
incr {Γ = Γ} {t' = t'} x (Map e' e pf) = Map (incr (FS x) e') (incr x e) pf
incrTuple x Unit        = Unit
incrTuple x (Pair e es) = Pair (incr x e) (incrTuple x es)
incrPatn x Abort       = Abort
incrPatn x (Case e es) = Case (incr (FS x) e) (incrPatn x es)

subst : {n tn : nat} {Γ : vect (type tn) n} {t t' : type tn} -> expr Γ t' -> (x : fin (Suc n)) -> expr (insertAt x Γ t') t -> expr Γ t
substTuple : {n tn m : nat} {Γ : vect (type tn) n} {ts : vect (type tn) m} {t' : type tn} -> expr Γ t' -> (x : fin (Suc n)) -> tuple (insertAt x Γ t') ts -> tuple Γ ts
substPatn : {n tn m : nat} {Γ : vect (type tn) n} {ts : vect (type tn) m} {t t' : type tn} -> expr Γ t' -> (x : fin (Suc n)) -> patn (insertAt x Γ t') ts t -> patn Γ ts t
subst {Γ = Γ} {t' = t'} e' x (Var y Refl)   with finEq y x
subst {Γ = Γ} {t' = t'} e' x (Var .x Refl)  | Yes Refl rewrite lookupInsertAt Γ x t' = e'
subst {Γ = Γ} {t' = t'} e' x (Var y Refl)   | No neq   = Var (fdecr x y neq) (sym (lookupInsertAtNeq Γ x y t' neq))
subst {Γ = Γ} {t' = t'} e' x Zero           = Zero
subst {Γ = Γ} {t' = t'} e' x (Suc e)        = Suc (subst e' x e)
subst {Γ = Γ} {t' = t'} e' x (Rec e eO eS)  = Rec (subst e' x e) (subst e' x eO) (subst (incr FZ (incr FZ e')) (FS (FS x)) eS)
subst {Γ = Γ} {t' = t'} e' x (Lam e)        = Lam (subst (incr FZ e') (FS x) e)
subst {Γ = Γ} {t' = t'} e' x (App e1 e2)    = App (subst e' x e1) (subst e' x e2)
subst {Γ = Γ} {t' = t'} e' x (Tuple es)     = Tuple (substTuple e' x es)
subst {Γ = Γ} {t' = t'} e' x (Proj y e)     = Proj y (subst e' x e)
subst {Γ = Γ} {t' = t'} e' x (Inj ts y e)   = Inj ts y (subst e' x e)
subst {Γ = Γ} {t' = t'} e' x (Match e es)   = Match (subst e' x e) (substPatn e' x es)
subst {Γ = Γ} {t' = t'} e' x (Map e'' e pf) = Map (subst (incr FZ e') (FS x) e'') (subst e' x e) pf
substTuple e' x Unit        = Unit
substTuple e' x (Pair e es) = Pair (subst e' x e) (substTuple e' x es)
substPatn e' x Abort       = Abort
substPatn e' x (Case e es) = Case (subst (incr FZ e') (FS x) e) (substPatn e' x es)
