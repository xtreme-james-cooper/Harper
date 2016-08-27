module Harper.Agda.Cha15Defs where

open import AgdaUtils.Nat
open import AgdaUtils.Fin
open import AgdaUtils.Vect
open import Harper.Agda.Cha15Type
open import Harper.Agda.Cha15Expr

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

