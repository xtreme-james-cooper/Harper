theory Chapter13_2_Typechecking
imports Chapter13_1_Language
begin

inductive types_from_pat :: "patn => type => type list => bool"
where tptrv [simp]: "types_from_pat PTriv Unit []"
    | tppar [simp]: "types_from_pat PPair (Prod t1 t2) [t1, t2]"
    | tpinl [simp]: "types_from_pat PInL (Sum t1 t2) [t1]"
    | tpinr [simp]: "types_from_pat PInR (Sum t1 t2) [t2]"
    | tpzer [simp]: "types_from_pat PZero Nat []"
    | tpsuc [simp]: "types_from_pat PSucc Nat [Nat]"

inductive_cases [elim!]: "types_from_pat PTriv t ts"
inductive_cases [elim!]: "types_from_pat PPair t ts"
inductive_cases [elim!]: "types_from_pat PInL t ts"
inductive_cases [elim!]: "types_from_pat PInR t ts"
inductive_cases [elim!]: "types_from_pat PZero t ts"
inductive_cases [elim!]: "types_from_pat PSucc t ts"

lemma [simp]: "types_from_pat p t ts ==> length ts = vars_count p"
by (induction p t ts rule: types_from_pat.induct, simp_all)

inductive typecheck :: "(nat, type) assoc => expr => type => bool"
      and typecheck_rules :: "(nat, type) assoc => rule list => type => type => bool"
      and typecheck_rule :: "(nat, type) assoc => rule => type => type => bool"
where tvar [simp]: "lookup env v = Some t ==> typecheck env (Var v) t"
    | tzer [simp]: "typecheck env Zero Nat"    
    | tsuc [simp]: "typecheck env n Nat ==> typecheck env (Succ n) Nat"
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
    | tcse [simp]: "typecheck env e t1 ==> typecheck_rules env rs t1 t2 ==> typecheck env (Case e t1 rs) t2" 
    | tnil [simp]: "typecheck_rules env [] t1 t2"
    | tcns [simp]: "typecheck_rule env r t1 t2 ==> typecheck_rules env rs t1 t2 ==> typecheck_rules env (r # rs) t1 t2"
    | trul [simp]: "types_from_pat p t1 ts ==> typecheck (extend_env ts env) e t2 ==> typecheck_rule env (Rule p e) t1 t2"

inductive_cases [elim!]: "typecheck e (Var x) t"
inductive_cases [elim!]: "typecheck e Zero t"
inductive_cases [elim!]: "typecheck e (Succ x) t"
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
inductive_cases [elim!]: "typecheck_rules e [] t t'"
inductive_cases [elim!]: "typecheck_rules e (r # rs) t t'"
inductive_cases [elim!]: "typecheck_rule e (Rule x y) t t'"

lemma [simp]: "typecheck env e t ==> typecheck (extend_at env n k) (incr_from n e) t"
  and [simp]: "typecheck_rules env rs t1 t2 ==> typecheck_rules (extend_at env n k) (incr_from_rules n rs) t1 t2"
  and [simp]: "typecheck_rule env r t1 t2 ==> typecheck_rule (extend_at env n k) (incr_from_rule n r) t1 t2"
proof (induction env e t and env rs t1 t2 and env r t1 t2 
       arbitrary: n and n and n 
       rule: typecheck_typecheck_rules_typecheck_rule.inducts)
case tvar
  thus ?case by (simp add: incr_def)
next case tzer
  thus ?case by simp
next case tsuc
  thus ?case by simp
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
next case (tcse env e t1 rs t2)
  hence "typecheck (extend_at env n k) (incr_from n e) t1" by simp
  moreover from tcse have "typecheck_rules (extend_at env n k) (incr_from_rules n rs) t1 t2" by simp
  ultimately show ?case by simp
next case tnil
  thus ?case by simp
next case tcns
  thus ?case by simp
next case (trul p t1 ts env e t2)
  from trul have "vars_count p = length ts" by simp
  moreover from trul have "typecheck (extend_at (extend_env ts env) (n + vars_count p) k) (incr_from (n + vars_count p) e) t2" by simp
  ultimately have "typecheck (extend_env ts (extend_at env n k)) (incr_from (n + vars_count p) e) t2" by simp
  with trul show ?case by simp
qed

lemma [simp]: "typecheck env e t ==> typecheck (extend_env ts env) (incr_by (length ts) e) t"
by (induction ts, simp_all)        

lemma [simp]: "typecheck (extend_at env n k) e t ==> n ~: free_vars e ==> typecheck env (sub_from n e) t"
  and [simp]: "typecheck_rules (extend_at env n k) rs t1 t2 ==> n ~: free_vars_rules rs ==> typecheck_rules env (sub_from_rules n rs) t1 t2"
  and [simp]: "typecheck_rule (extend_at env n k) r t1 t2 ==> n ~: free_vars_rule r ==> typecheck_rule env (sub_from_rule n r) t1 t2"
proof (induction "extend_at env n k" e t and "extend_at env n k" rs t1 t2 and "extend_at env n k" r t1 t2
       arbitrary: env n and env n and env n rule: typecheck_typecheck_rules_typecheck_rule.inducts)
case (tvar v t)
  thus ?case by (cases "v < n", simp, cases "v = n", simp_all)
next case tzer
  thus ?case by simp
next case tsuc
  thus ?case by simp
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
next case (tcse e t1 rs t2)
  hence "typecheck_rules env (sub_from_rules n rs) t1 t2" by simp 
  moreover from tcse have "typecheck env (sub_from n e) t1" by simp
  ultimately show ?case by simp
next case tnil
  thus ?case by simp
next case tcns
  thus ?case by simp
next case (trul p t1 ts)
  have "extend_at (extend_env ts env) (n + length ts) k = extend_env ts (extend_at env n k)" by simp
  with trul show ?case by simp
qed

lemma [simp]: "typecheck (extend env x t2) e t1 ==> typecheck env eb t2 ==> typecheck env (subst e eb x) t1"
  and [simp]: "typecheck_rules (extend env x t2) rs t1a t1b ==> typecheck env eb t2 ==> typecheck_rules env (subst_rules rs eb x) t1a t1b"
  and [simp]: "typecheck_rule (extend env x t2) r t1a t1b ==> typecheck env eb t2 ==> typecheck_rule env (subst_rule r eb x) t1a t1b"
proof (induction "extend env x t2" e t1 and "extend env x t2" rs t1a t1b and "extend env x t2" r t1a t1b
       arbitrary: env eb x and env eb x and env eb x rule: typecheck_typecheck_rules_typecheck_rule.inducts)
case tvar
  thus ?case by auto
next case tzer
  thus ?case by simp
next case tsuc
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
next case (tcse e t1 rs t2)
  hence "typecheck env (subst e eb x) t1" by simp
  moreover from tcse have "typecheck_rules env (subst_rules rs eb x) t1 t2" by simp
  ultimately show ?case by simp
next case tnil
  thus ?case by simp
next case tcns
  thus ?case by simp
next case (trul p t1 ts b t2')
  from trul have "typecheck env eb t2" by simp
  hence B: "typecheck (extend_env ts env) (incr_by (length ts) eb) t2" by simp
  from trul have A: "vars_count p = length ts" by simp
  hence "extend_env ts (extend env x t2) = extend (extend_env ts env) (x + vars_count p) t2" by simp
  with A B trul show ?case by simp
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
