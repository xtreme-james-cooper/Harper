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

primrec free_vars :: "expr => nat set"
where "free_vars (Var v) = {v}"
    | "free_vars Zero = {}"
    | "free_vars (Succ e) = free_vars e"
    | "free_vars (Rec e0 e1 et) = free_vars e0 Un free_vars et Un 
          ((%x. case x of 0 => 0 | Suc 0 => 0 | Suc (Suc k) => k) ` free_vars e1)"
    | "free_vars (Lam t b) = (%x. case x of 0 => 0 | Suc k => k) ` free_vars b"
    | "free_vars (Ap e1 e2) = free_vars e1 Un free_vars e2"

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

lemma inv_var: "typecheck env (Var v) t ==> lookup env v = Some t" 
by (induction env "Var v" t rule: typecheck.induct, simp)
lemma inv_zer: "typecheck env Zero t ==> t = Nat" 
by (induction env Zero t rule: typecheck.induct, simp)
lemma inv_suc: "typecheck env (Succ n) t ==> t = Nat & typecheck env n Nat"
by (induction env "Succ n" t rule: typecheck.induct, simp)
lemma inv_rec: "typecheck env (Rec e0 e1 e) t ==> typecheck env e Nat & typecheck env e0 t & typecheck (extend_at (extend_at env 0 Nat) 0 t) e1 t"
by (induction env "Rec e0 e1 e" t rule: typecheck.induct, simp)
lemma inv_lam: "typecheck env (Lam r e) t ==> EX t'. t = Arr r t' & typecheck (extend_at env 0 r) e t'"
by (induction env "Lam r e" t rule: typecheck.induct, simp)
lemma inv_app: "typecheck env (Ap e1 e2) t ==> EX t2. typecheck env e1 (Arr t2 t) & typecheck env e2 t2"
by (induction env "Ap e1 e2" t rule: typecheck.induct, auto)
                        
lemma [simp]: "typecheck env e t ==> typecheck (extend_at env n k) (incr_from n e) t"
proof (induction env e t arbitrary: n rule: typecheck.induct)
case tvar
  thus ?case by simp
next case tzer
  thus ?case by simp
next case tsuc
  thus ?case by simp
next case (trec env e e0 t e1)
  hence "typecheck (extend_at (extend_at (extend_at env 0 Nat) 0 t) (Suc (Suc n)) k) (incr_from (Suc (Suc n)) e1) t" by simp
  with trec show ?case by (simp add: extend_at_swap)
next case (tlam env r b t)
  hence "typecheck (extend_at (extend_at env 0 r) (Suc n) k) (incr_from (Suc n) b) t" by simp
  thus ?case by (simp add: extend_at_swap)
next case (tapp env e1 t2 t e2)
  from tapp have "typecheck (extend_at env n k) (incr_from n e1) (Arr t2 t)" by simp
  moreover from tapp have "typecheck (extend_at env n k) (incr_from n e2) t2" by simp
  ultimately show ?case by simp
qed

lemma typecheck_nofree: "typecheck env e t ==> k ~: free_vars e ==> typecheck (extend env k v) e t"
proof (induction env e t arbitrary: k rule: typecheck.induct)
case tvar
  thus ?case by simp
next case tzer
  thus ?case by simp
next case tsuc
  thus ?case by simp
next case (trec env e e0 t e1)
  have "Suc (Suc k) ~: free_vars e1"
  proof auto
    assume "Suc (Suc k) : free_vars e1"
    hence "!!f. k = f (Suc (Suc k)) ==> k : f`free_vars e1" by simp
    with trec show False by simp
  qed
  with trec show ?case by simp
next case (tlam env r b t)
  hence "Suc k ~: free_vars b"
  proof auto
    assume "Suc k : free_vars b"
    hence "!!f. k = f (Suc k) ==> k : f`free_vars b" by simp
    with tlam show False by simp
  qed
  with tlam show ?case by simp
next case (tapp env e1 t2 t e2)
  from tapp have "typecheck (extend env k v) e1 (Arr t2 t)" by simp
  moreover from tapp have "typecheck (extend env k v) e2 t2" by simp
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

primrec is_val :: "expr => bool"
where "is_val (Var v) = False"
    | "is_val Zero = True"
    | "is_val (Succ n) = is_val n"
    | "is_val (Rec e0 e1 et) = False"
    | "is_val (Lam t b) = True"
    | "is_val (Ap e1 e2) = False"

inductive eval :: "expr => expr => bool"
where esuc [simp]: "eval n n' ==> eval (Succ n) (Succ n')"
    | eap1 [simp]: "eval e1 e1' ==> eval (Ap e1 e2) (Ap e1' e2)"
    | eap2 [simp]: "is_val e1 ==> eval e2 e2' ==> eval (Ap e1 e2) (Ap e1 e2')"
    | eap3 [simp]: "is_val e2 ==> eval (Ap (Lam t b) e2) (subst b e2 0)"
    | erc1 [simp]: "eval e e' ==> eval (Rec e0 e1 e) (Rec e0 e1 e')"
    | erc2 [simp]: "eval (Rec e0 e1 Zero) e0"
    | erc3 [simp]: "is_val e ==> eval (Rec e0 e1 (Succ e)) (subst (subst e1 e 1) (Rec e0 e1 e) 0)"

lemma canonical_nat: "typecheck env e Nat ==> is_val e ==> e = Zero | (EX v. typecheck env v Nat & is_val v & e = Succ v)"
by (induction e, auto)

lemma canonical_arr: "typecheck env e (Arr t1 t2) ==> is_val e ==> (EX v. e = Lam t1 v & typecheck (extend_at env 0 t1) v t2)"
by (induction e, auto)

theorem preservation: "eval e e' ==> typecheck env e t ==> typecheck env e' t"
proof (induction e e' arbitrary: t rule: eval.induct)
case (esuc n n')
  moreover from esuc have "t = Nat" by (simp add: inv_suc)
  moreover from esuc have "typecheck env n Nat" by (simp add: inv_suc)
  ultimately show ?case by simp
next case (eap1 e1 e1' e2)
  with eap1 have "EX t2. typecheck env e1' (Arr t2 t) & typecheck env e2 t2" by (auto simp add: inv_app)
  thus ?case by auto
next case eap2
  thus ?case by auto
next case (eap3 e2 r b)
  hence "typecheck env (Ap (Lam r b) e2) t" by simp

  have "typecheck env (subst b e2 0) t" sorry
  thus ?case by simp
next case erc1
  thus ?case by auto
next case (erc2 e0 e1)
  from erc2 have "typecheck env Zero Nat & typecheck env e0 t & typecheck (extend_at (extend_at env 0 Nat) 0 t) e1 t" by (rule inv_rec)
  thus ?case by simp
next case (erc3 e e0 e1)
  thus ?case sorry
qed

theorem progress: "typecheck env e t ==> env = empty_map ==> is_val e | (EX e'. eval e e')"
proof (induct rule: typecheck.induct)
case tvar
  thus ?case by auto
next case tzer
  thus ?case by simp
next case (tsuc env n)
  thus ?case 
  proof (cases "is_val n")
  case True
    thus ?thesis by simp
  next case False
    from tsuc False have "\<exists>a. eval n a" by simp
    hence "\<exists>a. eval (Succ n) (Succ a)" sorry
    thus ?thesis by auto
  qed
next case trec
  thus ?case sorry
next case tlam
  thus ?case by simp
next case tapp
  thus ?case sorry
qed 


end
