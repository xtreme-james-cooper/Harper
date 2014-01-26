theory Chapter09
imports AssocList
begin

datatype type = Nat | Arr type type

datatype expr = 
  Var nat 
| Zero
| Succ expr
| Rec expr expr expr
| Lam type expr
| Ap expr expr

primrec incr_from :: "nat => expr => expr"
where "incr_from n (Var v) = Var (if v < n then v else Suc v)"
    | "incr_from n Zero = Zero"
    | "incr_from n (Succ e) = Succ (incr_from n e)"
    | "incr_from n (Rec e0 e1 et) = Rec (incr_from n e0) (incr_from (Suc (Suc n)) e1) (incr_from n et)"
    | "incr_from n (Lam t b) = Lam t (incr_from (Suc n) b)"
    | "incr_from n (Ap e1 e2) = Ap (incr_from n e1) (incr_from n e2)"

primrec subst :: "expr => expr => nat => expr"
where "subst (Var v) e x = (if v = x then e else Var v)"
    | "subst Zero e x = Zero"
    | "subst (Succ n) e x = Succ (subst n e x)"
    | "subst (Rec e0 e1 et) e x = Rec (subst e0 e x) (subst e1 (incr_from 0 (incr_from 0 e)) (Suc (Suc x))) (subst et e x)"
    | "subst (Lam t b) e x = Lam t (subst b (incr_from 0 e) (Suc x))"
    | "subst (Ap e1 e2) e x = Ap (subst e1 e x) (subst e2 e x)"

inductive typecheck :: "(nat, type) assoc => expr => type => bool"
where tvar [simp]: "lookup env v = Some t ==> typecheck env (Var v) t"
    | tzer [simp]: "typecheck env Zero Nat"    
    | tsuc [simp]: "typecheck env n Nat ==> typecheck env (Succ n) Nat"
    | trec [simp]: "typecheck env e Nat ==> typecheck env e0 t ==> 
                        typecheck (extend_at (extend_at env 0 Nat) 0 t) e1 t ==> 
                            typecheck env (Rec e0 e1 e) t"
    | tlam [simp]: "typecheck (extend_at env 0 r) e t ==> typecheck env (Lam r e) (Arr r t)"
    | tapp [simp]: "typecheck env e1 (Arr t2 t) ==> typecheck env e2 t2 ==> 
                        typecheck env (Ap e1 e2) t"

inductive_cases [elim!]: "typecheck e (Var x) t"
inductive_cases [elim!]: "typecheck e Zero t"
inductive_cases [elim!]: "typecheck e (Succ x) t"
inductive_cases [elim!]: "typecheck e (Rec x y z) t"
inductive_cases [elim!]: "typecheck e (Lam x y) t"
inductive_cases [elim!]: "typecheck e (Ap x y) t"

lemma [simp]: "typecheck env e t ==> typecheck (extend_at env n k) (incr_from n e) t"
proof (induction env e t arbitrary: n rule: typecheck.induct)
case tvar
  thus ?case by simp
next case tzer
  thus ?case by simp
next case tsuc
  thus ?case by simp
next case (trec env e e0 t e1)
  hence "typecheck (extend_at (extend_at (extend_at env 0 type.Nat) 0 t) (Suc (Suc n)) k) (incr_from (Suc (Suc n)) e1) t" by simp
  with trec show ?case by (simp add: extend_at_swap)
next case (tlam env r b t)
  hence "typecheck (extend_at (extend_at env 0 r) (Suc n) k) (incr_from (Suc n) b) t" by simp
  thus ?case by (simp add: extend_at_swap)
next case (tapp env e1 t2 t e2)
  from tapp have "typecheck (extend_at env n k) (incr_from n e1) (Arr t2 t)" by simp
  moreover from tapp have "typecheck (extend_at env n k) (incr_from n e2) t2" by simp
  ultimately show ?case by simp
qed

lemma typecheck_subst: "typecheck (extend env x t') e t ==> typecheck env e' t' ==> typecheck env (subst e e' x) t"
proof (induction "extend env x t'" e t arbitrary: env e' x rule: typecheck.induct)
case tvar
  thus ?case by auto
next case tzer
  thus ?case by simp
next case tsuc
  thus ?case by simp
next case trec
  thus ?case by simp
next case tlam
  thus ?case by simp
next case (tapp e1 t2 t e2)
  from tapp have "typecheck env (subst e1 e' x) (Arr t2 t)" by simp
  moreover from tapp have "typecheck env (subst e2 e' x) t2" by simp
  ultimately show ?case by simp
qed 

end
