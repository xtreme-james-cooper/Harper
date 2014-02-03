theory Chapter13_2_Typechecking
imports Chapter13_1_Language
begin

primrec extend_env :: "type list => (nat, type) assoc => (nat, type) assoc"
where "extend_env [] env = env"
    | "extend_env (t # ts) env = extend_env ts (extend_at env 0 t)"

inductive types_from_pat :: "patn => type => type list => bool"
where "types_from_pat Wild t []"
    | "types_from_pat PVar t [t]"
    | "types_from_pat PTriv Unit []"
    | "types_from_pat p1 t1 ts1 ==> types_from_pat p2 t2 ts2 ==> 
          types_from_pat (PPair p1 p2) (Prod t1 t2) (ts1 @ ts2)"
    | "types_from_pat p t1 ts ==> types_from_pat (PInL p) (Sum t1 t2) ts"
    | "types_from_pat p t2 ts ==> types_from_pat (PInR p) (Sum t1 t2) ts"

inductive_cases [elim!]: "types_from_pat Wild t ts"
inductive_cases [elim!]: "types_from_pat PVar t ts"
inductive_cases [elim!]: "types_from_pat PTriv t ts"
inductive_cases [elim!]: "types_from_pat (PPair p1 p2) t ts"
inductive_cases [elim!]: "types_from_pat (PInL p) t ts"
inductive_cases [elim!]: "types_from_pat (PInR p) t ts"

inductive typecheck :: "(nat, type) assoc => expr => type => bool"
      and typecheck_rules :: "(nat, type) assoc => rule list => type => type => bool"
      and typecheck_rule :: "(nat, type) assoc => rule => type => type => bool"
where tvar [simp]: "lookup env v = Some t ==> typecheck env (Var v) t"
    | tzer [simp]: "typecheck env Zero Nat"    
    | tsuc [simp]: "typecheck env n Nat ==> typecheck env (Succ n) Nat"
    | trec [simp]: "typecheck env e Nat ==> typecheck env e0 t ==> 
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
    | tmch [simp]: "typecheck env e t1 ==> typecheck_rules env rs t1 t2 ==> typecheck env (Match e rs) t2" 
    | tnil [simp]: "typecheck_rules env [] t1 t2"
    | tcns [simp]: "typecheck_rule env r t1 t2 ==> typecheck_rules env rs t1 t2 ==> typecheck_rules env (r # rs) t1 t2"
    | trul [simp]: "types_from_pat p t1 ts ==> typecheck (extend_env ts env) e t2 ==>  typecheck_rule env (Rule p e) t1 t2"

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
inductive_cases [elim!]: "typecheck e (Match x y) t"
inductive_cases [elim!]: "typecheck_rules e [] t t'"
inductive_cases [elim!]: "typecheck_rules e (r # rs) t t'"
inductive_cases [elim!]: "typecheck_rule e (Rule x y) t t'"
                        
thm typecheck_typecheck_rules_typecheck_rule.induct

lemma [simp]: "typecheck env e t ==> typecheck (extend_at env n k) (incr_from n e) t"
  and [simp]: "typecheck_rules env' rs t1 t2 ==> typecheck_rules (extend_at env' m k') (incr_from_rules m rs) t1 t2"
  and [simp]: "typecheck_rule env'' r t1' t2' ==> typecheck_rule (extend_at env'' p k'') (incr_from_rule p r) t1' t2'"
proof (induction env e t and env' rs t1 t2 and env'' r t1' t2' arbitrary: n and m and p rule: typecheck_typecheck_rules_typecheck_rule.inducts)
case (tvar env v t)
  thus ?case by (simp add: incr_def) (* TODO: remove incr_def? *)
next case tzer
  thus ?case by simp
next case tsuc
  thus ?case by simp
next case (trec env e e0 t e1)
  hence "typecheck (extend_at (extend_at env 0 Nat) (Suc n) k) (incr_from (Suc n) e1) t" by simp
  with trec show ?case by (simp add: extend_at_swap)
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
next case tmch
  thus ?case by simp sorry
next case tnil
  thus ?case by simp
next case tcns
  thus ?case by simp sorry
next case trul
  thus ?case by simp sorry
qed

lemma [simp]: "typecheck (extend_at env n k) e t ==> n ~: free_vars e ==> typecheck env (sub_from n e) t"
  and [simp]: "typecheck_rules (extend_at env' m k') rs t1 t2 ==> m ~: free_vars_rules rs ==> typecheck_rules env' (sub_from_rules m rs) t1 t2"
  and [simp]: "typecheck_rule (extend_at env'' p k'') r t1' t2' ==> p ~: free_vars_rule r ==> typecheck_rule env'' (sub_from_rule p r) t1' t2'"
proof (induction "extend_at env n k" e t and "extend_at env' m k'" rs t1 t2 and "extend_at env'' p k''" r t1' t2' arbitrary: env n and env' m and env'' p rule: typecheck_typecheck_rules_typecheck_rule.inducts)
case (tvar v t)
  thus ?case by (cases "v < n", simp, cases "v = n", simp_all)
next case tzer
  thus ?case by simp
next case tsuc
  thus ?case by simp
next case (trec e e0 t e1)
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
next case tmch
  thus ?case by simp sorry
next case tnil
  thus ?case by simp
next case tcns
  thus ?case by simp sorry
next case trul
  thus ?case by simp sorry
qed

lemma [simp]: "typecheck (extend env x t2) e t1 ==> typecheck env eb t2 ==> typecheck env (subst e eb x) t1"
  and [simp]: "typecheck_rules (extend env' x' t2) rs t1a t1b ==> typecheck env eb' t2 ==> typecheck_rules env' (subst_rules rs eb' x') t1a t1b"
  and [simp]: "typecheck_rule (extend env'' x'' t2) r t1a' t1b' ==> typecheck env eb'' t2 ==> typecheck_rule env'' (subst_rule r eb'' x'') t1a' t1b'"
proof (induction "extend env x t2" e t1 and "extend env' x' t2" rs t1a t1b and "extend env'' x'' t2" r t1a' t1b' 
       arbitrary: env eb x and env' eb' x' and env'' eb'' x'' rule: typecheck_typecheck_rules_typecheck_rule.inducts)
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
next case tmch
  thus ?case by simp sorry
next case tnil
  thus ?case by simp
next case tcns
  thus ?case by simp sorry
next case trul
  thus ?case by simp sorry
qed

lemma [simp]: "typecheck (extend_at env 0 t') e t ==> typecheck env e' t' ==> typecheck env (safe_subst e e') t"
proof (simp add: safe_subst_def)
  assume "typecheck (extend_at env 0 t') e t"
     and "typecheck env e' t'"
  thus "typecheck env (sub_from 0 (subst e (incr_from 0 e') 0)) t" by simp sorry
qed

