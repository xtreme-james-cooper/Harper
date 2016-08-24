module Harper.Agda.Cha09 where

open import AgdaUtils.Basics
open import AgdaUtils.Nat
open import AgdaUtils.Fin
open import AgdaUtils.Vect
open import AgdaUtils.Prod

data type : Set where
  Nat : type
  Arr : (t1 t2 : type) -> type

data expr {n : nat} (Γ : vect type n) : type -> Set where
  Var : {t : type} (x : fin n) (pf : Γ ! x == t) -> expr Γ t
  Zero : expr Γ Nat
  Suc : (e : expr Γ Nat) -> expr Γ Nat
  Rec : {t : type} (e : expr Γ Nat) (eO : expr Γ t) (eS : expr (Nat :: t :: Γ) t) -> expr Γ t
  Lam : {t1 t2 : type} (e : expr (t1 :: Γ) t2) -> expr Γ (Arr t1 t2)
  App : {t1 t2 : type} (e1 : expr Γ (Arr t1 t2)) (e2 : expr Γ t1)-> expr Γ t2

incr : {n : nat} {Γ : vect type n} {t t' : type} (x : fin (Suc n)) -> expr Γ t -> expr (insertAt x Γ t') t
incr x (Var y Refl)  = Var (fincr x y) (insertAtFincr _ y x _)
incr x Zero          = Zero
incr x (Suc e)       = Suc (incr x e)
incr x (Rec e eO eS) = Rec (incr x e) (incr x eO) (incr (FS (FS x)) eS)
incr x (Lam e)       = Lam (incr (FS x) e)
incr x (App e1 e2)   = App (incr x e1) (incr x e2)

subst : {n : nat} {Γ : vect type n} {t t' : type} -> expr Γ t' -> (x : fin (Suc n)) -> expr (insertAt x Γ t') t -> expr Γ t
subst {Γ = Γ} {t' = t'} e' x (Var y Refl)  with finEq y x
subst {Γ = Γ} {t' = t'} e' x (Var .x Refl) | Yes Refl rewrite lookupInsertAt Γ x t' = e'
subst {Γ = Γ} {t' = t'} e' x (Var y Refl)  | No neq   = Var (fdecr x y neq) (sym (lookupInsertAtNeq Γ x y t' neq))
subst {Γ = Γ} {t' = t'} e' x Zero          = Zero
subst {Γ = Γ} {t' = t'} e' x (Suc e)       = Suc (subst e' x e)
subst {Γ = Γ} {t' = t'} e' x (Rec e eO eS) = Rec (subst e' x e) (subst e' x eO) (subst (incr FZ (incr FZ e')) (FS (FS x)) eS)
subst {Γ = Γ} {t' = t'} e' x (Lam e)       = Lam (subst (incr FZ e') (FS x) e)
subst {Γ = Γ} {t' = t'} e' x (App e1 e2)   = App (subst e' x e1) (subst e' x e2)

data isVal {n : nat} {Γ : vect type n} : {t : type} -> expr Γ t -> Set where
  ZVal : isVal Zero
  SVal : (e : expr Γ Nat) -> isVal e -> isVal (Suc e)
  LamVal : {t1 t2 : type} (e : expr (t1 :: Γ) t2) -> isVal (Lam e)

data eval {n : nat} {Γ : vect type n} : {t : type} -> expr Γ t -> expr Γ t -> Set where
  EvSuc : {e e' : expr Γ Nat} -> eval e e' -> eval (Suc e) (Suc e')
  EvApp1 : {t1 t2 : type} {e1 e1' : expr Γ (Arr t1 t2)} {e2 : expr Γ t1} -> eval e1 e1' -> eval (App e1 e2) (App e1' e2)
  EvApp2 : {t1 t2 : type} {e1 : expr Γ (Arr t1 t2)} {e2 e2' : expr Γ t1} -> isVal e1 -> eval e2 e2' -> eval (App e1 e2) (App e1 e2')
  EvApp3 : {t1 t2 : type} {e1 : expr (t1 :: Γ) t2} {e2 : expr Γ t1} -> isVal e2 -> eval (App (Lam e1) e2) (subst e2 FZ e1)
  EvRec1 : {t : type} {e e' : expr Γ Nat} {eO : expr Γ t} {eS : expr (Nat :: t :: Γ) t} -> eval e e' -> eval (Rec e eO eS) (Rec e' eO eS)
  EvRec2 : {t : type} {eO : expr Γ t} {eS : expr (Nat :: t :: Γ) t} -> eval (Rec Zero eO eS) eO
  EvRec3 : {t : type} {e : expr Γ Nat} {eO : expr Γ t} {eS : expr (Nat :: t :: Γ) t} -> isVal e -> eval (Rec (Suc e) eO eS) (subst (Rec e eO eS) FZ (subst (incr FZ e) FZ eS))

evaluate : {t : type} (e : expr [] t) -> isVal e \/ (expr [] t * eval e)
evaluate (Var () pf)
evaluate Zero                 = InL ZVal
evaluate (Suc e)              with evaluate e
evaluate (Suc e)              | InL v         = InL (SVal e v)
evaluate (Suc e)              | InR (e' , ev) = InR (Suc e' , EvSuc ev)
evaluate (Rec e eO eS)        with evaluate e
evaluate (Rec .Zero eO eS)    | InL ZVal       = InR (eO , EvRec2)
evaluate (Rec .(Suc e) eO eS) | InL (SVal e v) = InR (subst (Rec e eO eS) FZ (subst (incr FZ e) FZ eS) , EvRec3 v)
evaluate (Rec e eO eS)        | InR (e' , ev)  = InR (Rec e' eO eS , EvRec1 ev)
evaluate (Lam e)              = InL (LamVal e)
evaluate (App e1 e2)          with evaluate e1
evaluate (App .(Lam e1) e2)   | InL (LamVal e1) with evaluate e2
evaluate (App .(Lam e1) e2)   | InL (LamVal e1) | InL v2         = InR (subst e2 FZ e1 , EvApp3 v2)
evaluate (App .(Lam e1) e2)   | InL (LamVal e1) | InR (e2' , ev) = InR (App (Lam e1) e2' , EvApp2 (LamVal e1) ev)
evaluate (App e1 e2)          | InR (e1' , ev) = InR (App e1' e2 , EvApp1 ev)
