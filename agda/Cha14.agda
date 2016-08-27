module Harper.Agda.Cha14 where

open import AgdaUtils.Basics
open import AgdaUtils.Nat
open import AgdaUtils.Fin
open import AgdaUtils.Vect
open import AgdaUtils.Prod
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

lookup : {n tn m : nat} {Γ : vect (type tn) n} {ts : vect (type tn) m} -> tuple Γ ts -> (x : fin m) -> expr Γ (ts ! x)
lookup Unit        ()
lookup (Pair e es) FZ     = e
lookup (Pair e es) (FS x) = lookup es x

match : {n tn m : nat} {Γ : vect (type tn) n} {ts : vect (type tn) m} {t : type tn} -> patn Γ ts t -> (x : fin m) -> expr ((ts ! x) :: Γ) t
match Abort       ()
match (Case e es) FZ     = e
match (Case e es) (FS x) = match es x 

prodSplit : {n tn m m' : nat} {Γ : vect (type tn) n} (ts : vect (type tn) m) (ts' : vect (type tn) m') (f : fin m -> fin m') -> expr Γ (Prod ts') -> 
  ((x : fin m) -> ts ! x == ts' ! f x) -> vect (type tn * expr Γ) m * λ es -> (x : fin m) -> fst (es ! x) == ts ! x
prodSplit {Γ = Γ} []        ts' f e pf = [] , λ ()
prodSplit {Γ = Γ} (t :: ts) ts' f e pf with prodSplit ts ts' (λ x -> f (FS x)) e (λ x -> pf (FS x)) 
prodSplit {Γ = Γ} (t :: ts) ts' f e pf | es , pf' = (t , coerce (Proj (f FZ) e)) :: es , (λ { FZ -> Refl ; (FS x) -> pf' x })
  where
    coerce : expr Γ (ts' ! f FZ) -> expr Γ t
    coerce e = cast e (funEq (expr Γ) (sym (pf FZ)))

prodCombine : {n tn m : nat} {Γ : vect (type tn) n} {t1 t2 : type tn} (ts : vect (type (Suc tn)) m) (es : vect (type tn * expr Γ) m) -> all (polytype FZ) ts -> 
  expr (t1 :: Γ) t2 -> ((x : fin m) -> fst (es ! x) == tsubstVect t1 FZ ts ! x) -> tuple Γ (tsubstVect t2 FZ ts)
prodCombine {Γ = Γ} {t1} []        []               TT           e' pf = Unit
prodCombine {Γ = Γ} {t1} (t :: ts) ((tt , e) :: es) (pft , pfts) e' pf rewrite pf FZ = Pair (Map e' e pft) (prodCombine ts es pfts e' (λ x -> pf (FS x)))

prodMap : {n tn m : nat} {Γ : vect (type tn) n} {t1 t2 : type tn} {ts : vect (type (Suc tn)) m} -> all (polytype FZ) ts -> 
  expr (t1 :: Γ) t2 -> expr Γ (Prod (tsubstVect t1 FZ ts)) -> expr Γ (Prod (tsubstVect t2 FZ ts))
prodMap {t1 = t1} {ts = ts} pf e' e with prodSplit (tsubstVect t1 FZ ts) (tsubstVect t1 FZ ts) (λ x -> x) e (λ x -> Refl)
prodMap {t1 = t1} {ts = ts} pf e' e | es , tspf = Tuple (prodCombine ts es pf e' tspf)

patternMap : {n tn m m' : nat} {Γ : vect (type tn) n} {t1 t2 : type tn} (ts : vect (type (Suc tn)) m) -> all (polytype FZ) ts -> (ts' : vect (type (Suc tn)) m') (f : fin m -> fin m') -> 
  expr (t1 :: Γ) t2 -> ((x : fin m) -> ts ! x == ts' ! f x) -> patn Γ (tsubstVect t1 FZ ts) (Sum (tsubstVect t2 FZ ts'))
patternMap {Γ = Γ} {t1} {t2} []        TT           ts' f e' pf = Abort
patternMap {Γ = Γ} {t1} {t2} (t :: ts) (pft , pfts) ts' f e' pf = 
  Case (Inj (tsubstVect t2 FZ ts') (f FZ) caseBody) (patternMap ts pfts ts' (λ x -> f (FS x)) e' (λ x -> pf (FS x)))
  where
    caseBody' : expr (tsubst t1 FZ t :: Γ) (tsubst t2 FZ t)
    caseBody' = Map (incr (FS FZ) e') (Var FZ Refl) pft
    caseBody : expr (tsubst t1 FZ t :: Γ) (tsubstVect t2 FZ ts' ! f FZ)
    caseBody rewrite tsubstVectLookup t2 ts' FZ (f FZ) = cast caseBody' (funEq (λ x -> expr (tsubst t1 FZ t :: Γ) (tsubst t2 FZ x)) (pf FZ))

sumMap : {n tn m : nat} {Γ : vect (type tn) n} {t1 t2 : type tn} {ts : vect (type (Suc tn)) m} -> all (polytype FZ) ts -> 
  expr (t1 :: Γ) t2 -> expr Γ (Sum (tsubstVect t1 FZ ts)) -> expr Γ (Sum (tsubstVect t2 FZ ts))
sumMap {ts = ts} pf e' e = Match e (patternMap ts pf ts (λ x -> x) e' (λ x -> Refl))

arrMap : {n tn : nat} {Γ : vect (type tn) n} {t1 t2 : type tn} (tt1 tt2 : type (Suc tn)) -> expr (t1 :: Γ) t2 -> expr Γ (Arr (tsubst t1 FZ tt1) (tsubst t1 FZ tt2)) -> 
  not (FZ ∈ tfreevars tt1) -> polytype FZ tt2 -> expr Γ (Arr (tsubst t2 FZ tt1) (tsubst t2 FZ tt2))
arrMap {t1 = t1} {t2} tt1 tt2 e' e pf1 pf2 = Lam (Map (incr (FS FZ) e') (App (incr FZ e) (Var FZ (tsubstNmemEq t2 t1 tt1 pf1))) pf2)

data isVal {n tn : nat} {Γ : vect (type tn) n} : {t : type tn} -> expr Γ t -> Set
data isTupleVal {n tn : nat} {Γ : vect (type tn) n} : {m : nat} {ts : vect (type tn) m} -> tuple Γ ts -> Set
data isVal {n} {tn} {Γ} where
  ZVal : isVal Zero
  SVal : (e : expr Γ Nat) -> isVal e -> isVal (Suc e)
  LamVal : {t1 t2 : type tn} (e : expr (t1 :: Γ) t2) -> isVal (Lam e)
  TupleVal : {m : nat} {ts : vect (type tn) m} (es : tuple Γ ts) -> isTupleVal es -> isVal (Tuple es)
  InjVal : {m : nat} (ts : vect (type tn) m) (x : fin m) (e : expr Γ (ts ! x)) -> isVal e -> isVal (Inj ts x e)
data isTupleVal {n} {tn} {Γ} where
  UnitVal : isTupleVal Unit
  PairVal : {t : type tn} {m : nat} {ts : vect (type tn) m} {e : expr Γ t} {es : tuple Γ ts} -> isVal e -> isTupleVal es -> isTupleVal (Pair e es)

data eval {n tn : nat} {Γ : vect (type tn) n} : {t : type tn} -> expr Γ t -> expr Γ t -> Set
data evalTuple {n tn : nat} {Γ : vect (type tn) n} : {m : nat} {ts : vect (type tn) m} -> tuple Γ ts -> tuple Γ ts -> Set
data eval {n} {tn} {Γ} where
  EvSuc : {e e' : expr Γ Nat} -> eval e e' -> eval (Suc e) (Suc e')
  EvApp1 : {t1 t2 : type tn} {e1 e1' : expr Γ (Arr t1 t2)} {e2 : expr Γ t1} -> eval e1 e1' -> eval (App e1 e2) (App e1' e2)
  EvApp2 : {t1 t2 : type tn} {e1 : expr Γ (Arr t1 t2)} {e2 e2' : expr Γ t1} -> isVal e1 -> eval e2 e2' -> eval (App e1 e2) (App e1 e2')
  EvApp3 : {t1 t2 : type tn} {e1 : expr (t1 :: Γ) t2} {e2 : expr Γ t1} -> isVal e2 -> eval (App (Lam e1) e2) (subst e2 FZ e1)
  EvRec1 : {t : type tn} {e e' : expr Γ Nat} {eO : expr Γ t} {eS : expr (Nat :: t :: Γ) t} -> eval e e' -> eval (Rec e eO eS) (Rec e' eO eS)
  EvRec2 : {t : type tn} {eO : expr Γ t} {eS : expr (Nat :: t :: Γ) t} -> eval (Rec Zero eO eS) eO
  EvRec3 : {t : type tn} {e : expr Γ Nat} {eO : expr Γ t} {eS : expr (Nat :: t :: Γ) t} -> isVal e -> 
    eval (Rec (Suc e) eO eS) (subst (Rec e eO eS) FZ (subst (incr FZ e) FZ eS))
  EvTup : {m : nat} {ts : vect (type tn) m} {es es' : tuple Γ ts} -> evalTuple es es' -> eval (Tuple es) (Tuple es')
  EvProj1 : {m : nat} {ts : vect (type tn) m} {x : fin m} {e e' : expr Γ (Prod ts)} -> eval e e' -> eval (Proj x e) (Proj x e')
  EvProj2 : {m : nat} {ts : vect (type tn) m} {x : fin m} {es : tuple Γ ts} -> eval (Proj x (Tuple es)) (lookup es x)
  EvInj : {m : nat}  {ts : vect (type tn) m} {x : fin m} {e e' : expr Γ (ts ! x)} -> eval e e' -> eval (Inj ts x e) (Inj ts x e')
  EvMatch1 : {t : type tn} {m : nat} {ts : vect (type tn) m} {e e' : expr Γ (Sum ts)} {es : patn Γ ts t} -> eval e e' -> eval (Match e es) (Match e' es)
  EvMatch2 : {t : type tn} {m : nat} {ts : vect (type tn) m} {x : fin m} {e : expr Γ (ts ! x)} {es : patn Γ ts t} -> 
    eval (Match (Inj ts x e) es) (subst e FZ (match es x))
  EvMapVar : {t1 t2 : type tn} {e' : expr (t1 :: Γ) t2} {e : expr Γ t1} -> eval (Map e' e PolyVar) (subst e FZ e')
  EvMapNat : {t1 t2 : type tn} {e' : expr (t1 :: Γ) t2} {e : expr Γ Nat} -> eval (Map e' e PolyNat) e
  EvMapProd : {t1 t2 : type tn} {m : nat} {ts : vect (type (Suc tn)) m} {e' : expr (t1 :: Γ) t2} {e : expr Γ (Prod (tsubstVect t1 FZ ts))} {pf : all (polytype FZ) ts} -> 
    eval (Map e' e (PolyProd pf)) (prodMap pf e' e)
  EvMapSum : {t1 t2 : type tn} {m : nat} {ts : vect (type (Suc tn)) m} {e' : expr (t1 :: Γ) t2} {e : expr Γ (Sum (tsubstVect t1 FZ ts))} {pf : all (polytype FZ) ts} -> 
    eval (Map e' e (PolySum pf)) (sumMap pf e' e)
  EvMapArr : {t1 t2 : type tn} {tt1 tt2 : type (Suc tn)} {e' : expr (t1 :: Γ) t2} {e : expr Γ (Arr (tsubst t1 FZ tt1) (tsubst t1 FZ tt2))} 
    {pf1 : not (FZ ∈ tfreevars tt1)} {pf2 : polytype FZ tt2} -> eval (Map e' e (PolyArr tt1 tt2 pf1 pf2)) (arrMap tt1 tt2 e' e pf1 pf2)
data evalTuple {n} {tn} {Γ} where
  EvTup1 : {t : type tn} {m : nat} {ts : vect (type tn) m} {e e' : expr Γ t} {es : tuple Γ ts} -> eval e e' -> evalTuple (Pair e es) (Pair e' es)
  EvTup2 : {t : type tn} {m : nat} {ts : vect (type tn) m} {e : expr Γ t} {es es' : tuple Γ ts} -> isVal e -> evalTuple es es' -> evalTuple (Pair e es) (Pair e es')

evaluate : {tn : nat} {t : type tn} (e : expr [] t) -> isVal e \/ (expr [] t * eval e)
evaluateTuple : {n tn : nat} {ts : vect (type tn) n} (es : tuple [] ts) -> isTupleVal es  \/ (tuple [] ts * evalTuple es)
evaluate (Var () pf)
evaluate Zero                               = InL ZVal
evaluate (Suc e)                            with evaluate e
evaluate (Suc e)                            | InL v         = InL (SVal e v)
evaluate (Suc e)                            | InR (e' , ev) = InR (Suc e' , EvSuc ev)
evaluate (Rec e eO eS)                      with evaluate e
evaluate (Rec .Zero eO eS)                  | InL ZVal       = InR (eO , EvRec2)
evaluate (Rec .(Suc e) eO eS)               | InL (SVal e v) = InR (subst (Rec e eO eS) FZ (subst (incr FZ e) FZ eS) , EvRec3 v)
evaluate (Rec e eO eS)                      | InR (e' , ev)  = InR (Rec e' eO eS , EvRec1 ev)
evaluate (Lam e)                            = InL (LamVal e)
evaluate (App e1 e2)                        with evaluate e1
evaluate (App .(Lam e1) e2)                 | InL (LamVal e1) with evaluate e2
evaluate (App .(Lam e1) e2)                 | InL (LamVal e1) | InL v2         = InR (subst e2 FZ e1 , EvApp3 v2)
evaluate (App .(Lam e1) e2)                 | InL (LamVal e1) | InR (e2' , ev) = InR (App (Lam e1) e2' , EvApp2 (LamVal e1) ev)
evaluate (App e1 e2)                        | InR (e1' , ev) = InR (App e1' e2 , EvApp1 ev)
evaluate (Tuple es)                         with evaluateTuple es
evaluate (Tuple es)                         | InL v          = InL (TupleVal es v)
evaluate (Tuple es)                         | InR (es' , ev) = InR (Tuple es' , (EvTup ev))
evaluate (Proj x e)                         with evaluate e
evaluate (Proj x .(Tuple es))               | InL (TupleVal es vs) = InR (lookup es x , EvProj2)
evaluate (Proj x e)                         | InR (e' , ev)        = InR (Proj x e' , EvProj1 ev)
evaluate (Inj ts x e)                       with evaluate e
evaluate (Inj ts x e)                       | InL v         = InL (InjVal ts x e v)
evaluate (Inj ts x e)                       | InR (e' , ev) = InR (Inj ts x e' , EvInj ev)
evaluate (Match e es)                       with evaluate e
evaluate (Match .(Inj ts x e) es)           | InL (InjVal ts x e  v) = InR (subst e FZ (match es x) , EvMatch2)
evaluate (Match e es)                       | InR (e' , ev)          = InR (Match e' es , EvMatch1 ev)
evaluate (Map e' e PolyVar)                 = InR (subst e FZ e' , EvMapVar)
evaluate (Map e' e PolyNat)                 = InR (e , EvMapNat)
evaluate (Map e' e (PolyProd pf))           = InR (prodMap pf e' e , EvMapProd)
evaluate (Map e' e (PolySum pf))            = InR (sumMap pf e' e , EvMapSum)
evaluate (Map e' e (PolyArr t1 t2 pf1 pf2)) = InR (arrMap t1 t2 e' e pf1 pf2 , EvMapArr)
evaluateTuple Unit        = InL UnitVal
evaluateTuple (Pair e es) with evaluate e
evaluateTuple (Pair e es) | InL v         with evaluateTuple es
evaluateTuple (Pair e es) | InL v         | InL vs         = InL (PairVal v vs)
evaluateTuple (Pair e es) | InL v         | InR (es' , ev) = InR (Pair e es' , EvTup2 v ev)
evaluateTuple (Pair e es) | InR (e' , ev) = InR (Pair e' es , EvTup1 ev)

-- definitions

unitT : {tn : nat} -> type tn
unitT = Prod []

pairT : {tn : nat} -> type tn -> type tn -> type tn
pairT t1 t2 = Prod (t1 :: t2 :: [])

voidT : {tn : nat} -> type tn
voidT = Sum []

plusT : {tn : nat} -> type tn -> type tn -> type tn
plusT t1 t2 = Sum (t1 :: t2 :: [])

boolT : {tn : nat} -> type tn
boolT = plusT unitT unitT

optT : {tn : nat} -> type tn -> type tn
optT t = plusT unitT t

unitE : {n tn : nat} {Γ : vect (type tn) n} -> expr Γ unitT
unitE = Tuple Unit

pairE : {n tn : nat} {Γ : vect (type tn) n} {t1 t2 : type tn} -> expr Γ t1 -> expr Γ t2 -> expr Γ (pairT t1 t2)
pairE e1 e2 = Tuple (Pair e1 (Pair e2 Unit))

projLE : {n tn : nat} {Γ : vect (type tn) n} {t1 t2 : type tn} -> expr Γ (pairT t1 t2) -> expr Γ t1
projLE e = Proj FZ e

projRE : {n tn : nat} {Γ : vect (type tn) n} {t1 t2 : type tn} -> expr Γ (pairT t1 t2) -> expr Γ t2
projRE e = Proj (FS FZ) e

abortE : {n tn : nat} {Γ : vect (type tn) n} {t : type tn} -> expr Γ voidT -> expr Γ t
abortE e = Match e Abort

inLE : {n tn : nat} {Γ : vect (type tn) n} {t1 t2 : type tn} -> expr Γ t1 -> expr Γ (plusT t1 t2)
inLE {t1 = t1} {t2} e = Inj (t1 :: t2 :: []) FZ e

inRE : {n tn : nat} {Γ : vect (type tn) n} {t1 t2 : type tn} -> expr Γ t2 -> expr Γ (plusT t1 t2)
inRE {t1 = t1} {t2} e = Inj (t1 :: t2 :: []) (FS FZ) e 

casesE : {n tn : nat} {Γ : vect (type tn) n} {t1 t2 t : type tn} -> expr Γ (plusT t1 t2) -> expr (t1 :: Γ) t -> expr (t2 :: Γ) t -> expr Γ t
casesE e eL eR = Match e (Case eL (Case eR Abort))

trueE : {n tn : nat} {Γ : vect (type tn) n} -> expr Γ boolT
trueE = inLE unitE

falseE : {n tn : nat} {Γ : vect (type tn) n} -> expr Γ boolT
falseE = inRE unitE

ifE : {n tn : nat} {Γ : vect (type tn) n} {t : type tn} -> expr Γ boolT -> expr Γ t -> expr Γ t -> expr Γ t
ifE eB eT eF = casesE eB (incr FZ eT) (incr FZ eF)

noneE : {n tn : nat} {Γ : vect (type tn) n} {t : type tn} -> expr Γ (optT t)
noneE = inLE unitE

someE : {n tn : nat} {Γ : vect (type tn) n} {t : type tn} -> expr Γ t -> expr Γ (optT t)
someE e = inRE e

orElseE : {n tn : nat} {Γ : vect (type tn) n} {t t' : type tn} -> expr Γ (optT t) -> expr Γ t' -> expr (t :: Γ) t' -> expr Γ t'
orElseE eO eN eS = casesE eO (incr FZ eN) eS

