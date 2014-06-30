theory Chapter16_2_Typechecking
imports Chapter16_1_Language
begin

inductive typecheck :: "(nat, type) assoc => expr => type => bool"
where tvar [simp]: "lookup env v = Some t ==> typecheck env (Var v) t"
    | tzer [simp]: "typecheck env Zero Nat"    
    | tsuc [simp]: "typecheck env n Nat ==> typecheck env (Succ n) Nat"
    | tisz [simp]: "typecheck env e Nat ==> typecheck env e0 t ==> 
                        typecheck (extend_at env 0 Nat) e1 t ==> 
                            typecheck env (IsZ e0 e1 e) t"
    | tlam [simp]: "typecheck (extend_at env 0 r) e t ==> typecheck env (Lam r e) (Arr r t)"
    | tapp [simp]: "typecheck env e1 (Arr t2 t) ==> typecheck env e2 t2 ==> 
                        typecheck env (Ap e1 e2) t"
    | tfix [simp]: "typecheck (extend_at env 0 t) b t ==> typecheck env (Fix t b) t"
    | ttrv [simp]: "typecheck env Triv Unit"
    | tpar [simp]: "typecheck env e1 t1 ==> typecheck env e2 t2 ==> typecheck env (Pair e1 e2) (Prod t1 t2)"
    | tprl [simp]: "typecheck env e (Prod t1 t2) ==> typecheck env (ProjL e) t1"
    | tprr [simp]: "typecheck env e (Prod t1 t2) ==> typecheck env (ProjR e) t2"
    | tabt [simp]: "typecheck env e Void ==> typecheck env (Abort t e) t"
    | tinl [simp]: "typecheck env e t1 ==> typecheck env (InL t1 t2 e) (Sum t1 t2)"
    | tinr [simp]: "typecheck env e t2 ==> typecheck env (InR t1 t2 e) (Sum t1 t2)"
    | tcse [simp]: "typecheck env e (Sum t1 t2) ==> typecheck (extend_at env 0 t1) el t ==> 
                        typecheck (extend_at env 0 t2) er t ==> typecheck env (Case e el er) t"

inductive_cases [elim!]: "typecheck e (Var x) t"
inductive_cases [elim!]: "typecheck e Zero t"
inductive_cases [elim!]: "typecheck e (Succ x) t"
inductive_cases [elim!]: "typecheck e (IsZ x y z) t"
inductive_cases [elim!]: "typecheck e (Lam x y) t"
inductive_cases [elim!]: "typecheck e (Ap x y) t"
inductive_cases [elim!]: "typecheck e (Fix x y) t"
inductive_cases [elim!]: "typecheck e Triv t"
inductive_cases [elim!]: "typecheck e (Pair x y) t"
inductive_cases [elim!]: "typecheck e (ProjL x) t"
inductive_cases [elim!]: "typecheck e (ProjR x) t"
inductive_cases [elim!]: "typecheck e (Abort x y) t"
inductive_cases [elim!]: "typecheck e (InL x y z) t"
inductive_cases [elim!]: "typecheck e (InR x y z) t"
inductive_cases [elim!]: "typecheck e (Case x y z) t"

lemma [simp]: "typecheck env e t ==> typecheck (extend_at env n k) (incr_from n e) t"
proof (induction env e t arbitrary: n rule: typecheck.inducts)
case tvar
  thus ?case by (simp add: incr_def)
next case tzer
  thus ?case by simp
next case tsuc
  thus ?case by simp
next case (tisz env e e0 t e1)
  hence "typecheck (extend_at (extend_at env 0 Nat) (Suc n) k) (incr_from (Suc n) e1) t" by simp
  with tisz show ?case by (simp add: extend_at_swap)
next case (tlam env r b t)
  hence "typecheck (extend_at (extend_at env 0 r) (Suc n) k) (incr_from (Suc n) b) t" by simp
  thus ?case by (simp add: extend_at_swap)
next case (tapp env e1 t2 t e2)
  from tapp have "typecheck (extend_at env n k) (incr_from n e1) (Arr t2 t)" by simp
  moreover from tapp have "typecheck (extend_at env n k) (incr_from n e2) t2" by simp
  ultimately show ?case by simp
next case (tfix env t b)
  hence "typecheck (extend_at (extend_at env 0 t) (Suc n) k) (incr_from (Suc n) b) t" by simp
  thus ?case by (simp add: extend_at_swap)
next case ttrv
  thus ?case by simp
next case tpar
  thus ?case by simp
next case (tprl env e t1 t2)
  hence "typecheck (extend_at env n k) (incr_from n e) (Prod t1 t2)" by simp
  thus ?case by simp 
next case (tprr env e t1 t2)
  hence "typecheck (extend_at env n k) (incr_from n e) (Prod t1 t2)" by simp
  thus ?case by simp
next case tabt
  thus ?case by simp
next case tinl
  thus ?case by simp
next case tinr
  thus ?case by simp
next case (tcse env e t1 t2 el t er)
  hence "typecheck (extend_at env n k) (incr_from n e) (Sum t1 t2)" by simp 
  moreover from tcse have "typecheck (extend_at (extend_at env 0 t1) (Suc n) k) (incr_from (Suc n) el) t" by simp
  moreover from tcse have "typecheck (extend_at (extend_at env 0 t2) (Suc n) k) (incr_from (Suc n) er) t" by simp
  ultimately show ?case by (simp add: extend_at_swap)
qed

lemma [simp]: "typecheck env e t ==> typecheck (extend_env ts env) (incr_by (length ts) e) t"
by (induction ts, simp_all)        

lemma [simp]: "typecheck (extend_at env n k) e t ==> n ~: free_vars e ==> typecheck env (sub_from n e) t"
proof (induction "extend_at env n k" e t arbitrary: env n rule: typecheck.inducts)
case (tvar v t)
  thus ?case by (cases "v < n", simp, cases "v = n", simp_all)
next case tzer
  thus ?case by simp
next case tsuc
  thus ?case by simp
next case (tisz e e0 t e1)
  moreover hence "Suc n ~: free_vars e1" by auto
  moreover have "extend_at (extend_at env n k) 0 Nat = extend_at (extend_at env 0 Nat) (Suc n) k" by (simp add: extend_at_swap)
  ultimately show ?case by simp
next case tlam
  thus ?case by (simp add: extend_at_swap)
next case (tapp e1 t2 t e2)
  from tapp have "typecheck env (sub_from n e1) (Arr t2 t)" by simp
  moreover from tapp have "typecheck env (sub_from n e2) t2" by simp
  ultimately show ?case by simp
next case tfix
  thus ?case by (simp add: extend_at_swap)
next case ttrv
  thus ?case by simp
next case tpar
  thus ?case by simp
next case (tprl e t1 t2)
  hence "typecheck env (sub_from n e) (Prod t1 t2)" by simp
  thus ?case by simp
next case (tprr e t1 t2)
  hence "typecheck env (sub_from n e) (Prod t1 t2)" by simp
  thus ?case by simp
next case tabt
  thus ?case by simp
next case tinl
  thus ?case by simp
next case tinr
  thus ?case by simp
next case (tcse e t1 t2 el t er)
  hence "typecheck env (sub_from n e) (Sum t1 t2)" by simp 
  moreover from tcse have "typecheck (extend_at env 0 t1) (sub_from (Suc n) el) t" by (simp add: extend_at_swap)
  moreover from tcse have "typecheck (extend_at env 0 t2) (sub_from (Suc n) er) t" by (simp add: extend_at_swap)
  ultimately show ?case by simp
qed

lemma [simp]: "typecheck (extend env x t2) e t1 ==> typecheck env eb t2 ==> typecheck env (subst e eb x) t1"
proof (induction "extend env x t2" e t1 arbitrary: env eb x rule: typecheck.inducts)
case tvar
  thus ?case by auto
next case tzer
  thus ?case by simp
next case tsuc
  thus ?case by simp
next case tisz
  thus ?case by simp
next case tlam
  thus ?case by simp
next case (tapp e1 t2 t e2)
  from tapp have "typecheck env (subst e1 eb x) (Arr t2 t)" by simp
  moreover from tapp have "typecheck env (subst e2 eb x) t2" by simp
  ultimately show ?case by simp
next case tfix
  thus ?case by simp
next case ttrv
  thus ?case by simp
next case tpar
  thus ?case by simp
next case (tprl e t1 t2)
  hence "typecheck env (subst e eb x) (Prod t1 t2)" by simp
  thus ?case by simp
next case (tprr e t1 t2)
  hence "typecheck env (subst e eb x) (Prod t1 t2)" by simp
  thus ?case by simp
next case tabt
  thus ?case by simp
next case tinl
  thus ?case by simp
next case tinr
  thus ?case by simp
next case (tcse e t1 t2 el t er)
  hence "typecheck env (subst e eb x) (Sum t1 t2)" by (simp add: extend_at_swap) 
  moreover from tcse have "typecheck (extend_at env 0 t1) (subst el (incr_from 0 eb) (Suc x)) t" by (simp add: extend_at_swap) 
  moreover from tcse have "typecheck (extend_at env 0 t2) (subst er (incr_from 0 eb) (Suc x)) t" by (simp add: extend_at_swap) 
  ultimately show ?case by simp
qed

lemma [simp]: "typecheck (extend_at env 0 t') e t ==> typecheck env e' t' ==> typecheck env (safe_subst e e') t"
by (simp add: safe_subst_def)

inductive typecheck_subst :: "(nat, type) assoc => expr list => type list => bool"
where tsubn [simp]: "typecheck_subst env [] []"
    | tsubc [simp]: "typecheck env e t ==> typecheck_subst env es ts ==> typecheck_subst env (e # es) (t # ts)"

inductive_cases [elim!]: "typecheck_subst e [] t"
inductive_cases [elim!]: "typecheck_subst e (x # y) t"

lemma [simp]: "typecheck_subst env e1 t1 ==> typecheck_subst env e2 t2 ==> typecheck_subst env (e1 @ e2) (t1 @ t2)"
by (induction env e1 t1 rule: typecheck_subst.induct, simp_all)

lemma [simp]: "typecheck_subst env ss ts ==> length ss = length ts"
by (induction env ss ts rule: typecheck_subst.induct, simp_all)

primrec apply_subst :: "expr list => expr => expr"
where "apply_subst [] e = e"
    | "apply_subst (e' # e's) e = apply_subst e's (safe_subst e (incr_by (length e's) e'))"

lemma [simp]: "typecheck_subst env s ts ==> typecheck (extend_env ts env) e t ==> typecheck env (apply_subst s e) t"
by (induction env s ts arbitrary: e rule: typecheck_subst.induct, simp_all)

end
