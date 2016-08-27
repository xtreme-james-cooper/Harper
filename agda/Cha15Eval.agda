module Harper.Agda.Cha15Eval where

open import AgdaUtils.Basics
open import AgdaUtils.Nat
open import AgdaUtils.Fin
open import AgdaUtils.Vect
open import AgdaUtils.Prod
open import AgdaUtils.SetsB
open import Harper.Agda.Cha15Type
open import Harper.Agda.Cha15Expr

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
