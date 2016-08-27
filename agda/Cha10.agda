module Harper.Agda.Cha10 where

open import AgdaUtils.Basics
open import AgdaUtils.Nat
open import AgdaUtils.Fin
open import AgdaUtils.Vect
open import AgdaUtils.Prod

data type : Set where
  Nat : type
  Arr : (t1 t2 : type) -> type
  Prod : {n : nat} (ts : vect type n) -> type

data expr {n : nat} (Γ : vect type n) : type -> Set
data tuple {n : nat} (Γ : vect type n) : {m : nat} -> vect type m -> Set
data expr {n} Γ where
  Var : {t : type} (x : fin n) (pf : Γ ! x == t) -> expr Γ t
  Zero : expr Γ Nat
  Suc : (e : expr Γ Nat) -> expr Γ Nat
  Rec : {t : type} (e : expr Γ Nat) (eO : expr Γ t) (eS : expr (Nat :: t :: Γ) t) -> expr Γ t
  Lam : {t1 t2 : type} (e : expr (t1 :: Γ) t2) -> expr Γ (Arr t1 t2)
  App : {t1 t2 : type} (e1 : expr Γ (Arr t1 t2)) (e2 : expr Γ t1) -> expr Γ t2
  Tuple : {m : nat} {ts : vect type m} (es : tuple Γ ts) -> expr Γ (Prod ts)
  Proj : {t : type} {m : nat} {ts : vect type m} (x : fin m) (e : expr Γ (Prod ts)) (pf : ts ! x == t) -> expr Γ t  
data tuple {n} Γ where
  Unit : tuple Γ []
  Pair : {t : type} {m : nat} {ts : vect type m} (e : expr Γ t) (es : tuple Γ ts) -> tuple Γ (t :: ts)

incr : {n : nat} {Γ : vect type n} {t t' : type} (x : fin (Suc n)) -> expr Γ t -> expr (insertAt x Γ t') t
incrTuple : {n m : nat} {Γ : vect type n} {ts : vect type m} {t' : type} (x : fin (Suc n)) -> tuple Γ ts -> tuple (insertAt x Γ t') ts
incr {Γ = Γ} {t' = t'} x (Var y Refl)  = Var (fincr x y) (insertAtFincr Γ y x t')
incr {Γ = Γ} {t' = t'} x Zero          = Zero
incr {Γ = Γ} {t' = t'} x (Suc e)       = Suc (incr x e)
incr {Γ = Γ} {t' = t'} x (Rec e eO eS) = Rec (incr x e) (incr x eO) (incr (FS (FS x)) eS)
incr {Γ = Γ} {t' = t'} x (Lam e)       = Lam (incr (FS x) e)
incr {Γ = Γ} {t' = t'} x (App e1 e2)   = App (incr x e1) (incr x e2)
incr {Γ = Γ} {t' = t'} x (Tuple es)    = Tuple (incrTuple x es)
incr {Γ = Γ} {t' = t'} x (Proj y e pf) = Proj y (incr x e) pf
incrTuple x Unit        = Unit
incrTuple x (Pair e es) = Pair (incr x e) (incrTuple x es)

subst : {n : nat} {Γ : vect type n} {t t' : type} -> expr Γ t' -> (x : fin (Suc n)) -> expr (insertAt x Γ t') t -> expr Γ t
substTuple : {n m : nat} {Γ : vect type n} {ts : vect type m} {t' : type} -> expr Γ t' -> (x : fin (Suc n)) -> tuple (insertAt x Γ t') ts -> tuple Γ ts
subst {Γ = Γ} {t' = t'} e' x (Var y Refl)  with finEq y x
subst {Γ = Γ} {t' = t'} e' x (Var .x Refl) | Yes Refl rewrite lookupInsertAt Γ x t' = e'
subst {Γ = Γ} {t' = t'} e' x (Var y Refl)  | No neq   = Var (fdecr x y neq) (sym (lookupInsertAtNeq Γ x y t' neq))
subst {Γ = Γ} {t' = t'} e' x Zero          = Zero
subst {Γ = Γ} {t' = t'} e' x (Suc e)       = Suc (subst e' x e)
subst {Γ = Γ} {t' = t'} e' x (Rec e eO eS) = Rec (subst e' x e) (subst e' x eO) (subst (incr FZ (incr FZ e')) (FS (FS x)) eS)
subst {Γ = Γ} {t' = t'} e' x (Lam e)       = Lam (subst (incr FZ e') (FS x) e)
subst {Γ = Γ} {t' = t'} e' x (App e1 e2)   = App (subst e' x e1) (subst e' x e2)
subst {Γ = Γ} {t' = t'} e' x (Tuple es)    = Tuple (substTuple e' x es)
subst {Γ = Γ} {t' = t'} e' x (Proj y e pf) = Proj y (subst e' x e) pf
substTuple e' x Unit        = Unit
substTuple e' x (Pair e es) = Pair (subst e' x e) (substTuple e' x es)

lookup : {n m : nat} {Γ : vect type n} {ts : vect type m} -> tuple Γ ts -> (x : fin m) -> expr Γ (ts ! x)
lookup Unit        ()
lookup (Pair e es) FZ     = e
lookup (Pair e es) (FS x) = lookup es x

data isVal {n : nat} {Γ : vect type n} : {t : type} -> expr Γ t -> Set
data isTupleVal {n : nat} {Γ : vect type n} : {m : nat} {ts : vect type m} -> tuple Γ ts -> Set
data isVal {n} {Γ} where
  ZVal : isVal Zero
  SVal : (e : expr Γ Nat) -> isVal e -> isVal (Suc e)
  LamVal : {t1 t2 : type} (e : expr (t1 :: Γ) t2) -> isVal (Lam e)
  TupleVal : {m : nat} {ts : vect type m} (es : tuple Γ ts) -> isTupleVal es -> isVal (Tuple es)
data isTupleVal {n} {Γ} where
  UnitVal : isTupleVal Unit
  PairVal : {t : type} {m : nat} {ts : vect type m} {e : expr Γ t} {es : tuple Γ ts} -> isVal e -> isTupleVal es -> isTupleVal (Pair e es)

data eval {n : nat} {Γ : vect type n} : {t : type} -> expr Γ t -> expr Γ t -> Set
data evalTuple {n : nat} {Γ : vect type n} : {m : nat} {ts : vect type m} -> tuple Γ ts -> tuple Γ ts -> Set
data eval {n} {Γ} where
  EvSuc : {e e' : expr Γ Nat} -> eval e e' -> eval (Suc e) (Suc e')
  EvApp1 : {t1 t2 : type} {e1 e1' : expr Γ (Arr t1 t2)} {e2 : expr Γ t1} -> eval e1 e1' -> eval (App e1 e2) (App e1' e2)
  EvApp2 : {t1 t2 : type} {e1 : expr Γ (Arr t1 t2)} {e2 e2' : expr Γ t1} -> isVal e1 -> eval e2 e2' -> eval (App e1 e2) (App e1 e2')
  EvApp3 : {t1 t2 : type} {e1 : expr (t1 :: Γ) t2} {e2 : expr Γ t1} -> isVal e2 -> eval (App (Lam e1) e2) (subst e2 FZ e1)
  EvRec1 : {t : type} {e e' : expr Γ Nat} {eO : expr Γ t} {eS : expr (Nat :: t :: Γ) t} -> eval e e' -> eval (Rec e eO eS) (Rec e' eO eS)
  EvRec2 : {t : type} {eO : expr Γ t} {eS : expr (Nat :: t :: Γ) t} -> eval (Rec Zero eO eS) eO
  EvRec3 : {t : type} {e : expr Γ Nat} {eO : expr Γ t} {eS : expr (Nat :: t :: Γ) t} -> isVal e -> eval (Rec (Suc e) eO eS) (subst (Rec e eO eS) FZ (subst (incr FZ e) FZ eS))
  EvTup : {m : nat} {ts : vect type m} {es es' : tuple Γ ts} -> evalTuple es es' -> eval (Tuple es) (Tuple es')
  EvProj1 : {t : type} {m : nat} {ts : vect type m} {x : fin m} {e e' : expr Γ (Prod ts)} {pf : ts ! x == t} -> eval e e' -> eval (Proj x e pf) (Proj x e' pf)
  EvProj2 : {t : type} {m : nat} {ts : vect type m} {x : fin m} {es : tuple Γ ts} {pf : ts ! x == t} -> eval (Proj x (Tuple es) pf) (cast (lookup es x) (funEq (expr Γ) pf))
data evalTuple {n} {Γ} where
  EvTup1 : {t : type} {m : nat} {ts : vect type m} {e e' : expr Γ t} {es : tuple Γ ts} -> eval e e' -> evalTuple (Pair e es) (Pair e' es)
  EvTup2 : {t : type} {m : nat} {ts : vect type m} {e : expr Γ t} {es es' : tuple Γ ts} -> isVal e -> evalTuple es es' -> evalTuple (Pair e es) (Pair e es')

evaluate : {t : type} (e : expr [] t) -> isVal e \/ (expr [] t * eval e)
evaluateTuple : {n : nat} {ts : vect type n} (es : tuple [] ts) -> isTupleVal es  \/ (tuple [] ts * evalTuple es)
evaluate (Var () pf)
evaluate Zero                      = InL ZVal
evaluate (Suc e)                   with evaluate e
evaluate (Suc e)                   | InL v         = InL (SVal e v)
evaluate (Suc e)                   | InR (e' , ev) = InR (Suc e' , EvSuc ev)
evaluate (Rec e eO eS)             with evaluate e
evaluate (Rec .Zero eO eS)         | InL ZVal       = InR (eO , EvRec2)
evaluate (Rec .(Suc e) eO eS)      | InL (SVal e v) = InR (subst (Rec e eO eS) FZ (subst (incr FZ e) FZ eS) , EvRec3 v)
evaluate (Rec e eO eS)             | InR (e' , ev)  = InR (Rec e' eO eS , EvRec1 ev)
evaluate (Lam e)                   = InL (LamVal e)
evaluate (App e1 e2)               with evaluate e1
evaluate (App .(Lam e1) e2)        | InL (LamVal e1) with evaluate e2
evaluate (App .(Lam e1) e2)        | InL (LamVal e1) | InL v2         = InR (subst e2 FZ e1 , EvApp3 v2)
evaluate (App .(Lam e1) e2)        | InL (LamVal e1) | InR (e2' , ev) = InR (App (Lam e1) e2' , EvApp2 (LamVal e1) ev)
evaluate (App e1 e2)               | InR (e1' , ev) = InR (App e1' e2 , EvApp1 ev)
evaluate (Tuple es)                with evaluateTuple es
evaluate (Tuple es)                | InL v          = InL (TupleVal es v)
evaluate (Tuple es)                | InR (es' , ev) = InR (Tuple es' , (EvTup ev))
evaluate (Proj x e pf)             with evaluate e
evaluate (Proj x .(Tuple es) Refl) | InL (TupleVal es vs) = InR (lookup es x , EvProj2)
evaluate (Proj x e pf)             | InR (e' , ev)        = InR (Proj x e' pf , EvProj1 ev)
evaluateTuple Unit        = InL UnitVal
evaluateTuple (Pair e es) with evaluate e
evaluateTuple (Pair e es) | InL v         with evaluateTuple es
evaluateTuple (Pair e es) | InL v         | InL vs         = InL (PairVal v vs)
evaluateTuple (Pair e es) | InL v         | InR (es' , ev) = InR (Pair e es' , EvTup2 v ev)
evaluateTuple (Pair e es) | InR (e' , ev) = InR (Pair e' es , EvTup1 ev)

-- definitions 

unitT : type
unitT = Prod []

pairT : type -> type -> type
pairT t1 t2 = Prod (t1 :: t2 :: [])

unitE : {n : nat} {Γ : vect type n} -> expr Γ unitT
unitE = Tuple Unit

pairE : {n : nat} {Γ : vect type n} {t1 t2 : type} -> expr Γ t1 -> expr Γ t2 -> expr Γ (pairT t1 t2)
pairE e1 e2 = Tuple (Pair e1 (Pair e2 Unit))

projLE : {n : nat} {Γ : vect type n} {t1 t2 : type} -> expr Γ (pairT t1 t2) -> expr Γ t1
projLE e = Proj FZ e Refl

projRE : {n : nat} {Γ : vect type n} {t1 t2 : type} -> expr Γ (pairT t1 t2) -> expr Γ t2
projRE e = Proj (FS FZ) e Refl