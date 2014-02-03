theory Chapter13_2_Typechecking
imports Chapter13_1_Language
begin

datatype constr = 
  All
| And constr constr
| Nothing
| Or constr constr
| CInL type type constr
| CInR type type constr
| CTriv
| CPair constr constr

inductive typecheck_constr :: "constr => type => bool"
where [simp]: "typecheck_constr All t"
    | [simp]: "typecheck_constr c1 t ==> typecheck_constr c2 t ==> typecheck_constr (And c1 c2) t"
    | [simp]: "typecheck_constr Nothing t"
    | [simp]: "typecheck_constr c1 t ==> typecheck_constr c2 t ==> typecheck_constr (Or c1 c2) t"
    | [simp]: "typecheck_constr c t1 ==> typecheck_constr (CInL t1 t2 c) (Sum t1 t2)"
    | [simp]: "typecheck_constr c t2 ==> typecheck_constr (CInR t1 t2 c) (Sum t1 t2)"
    | [simp]: "typecheck_constr CTriv Unit"
    | [simp]: "typecheck_constr c1 t1 ==> typecheck_constr c2 t2 ==> typecheck_constr (CPair c1 c2) (Prod t1 t2)"

inductive_cases [elim!]: "typecheck_constr All t"
inductive_cases [elim!]: "typecheck_constr (And x y) t"
inductive_cases [elim!]: "typecheck_constr Nothing t"
inductive_cases [elim!]: "typecheck_constr (Or x y) t"
inductive_cases [elim!]: "typecheck_constr (CInL x y z) t"
inductive_cases [elim!]: "typecheck_constr (CInR x y z) t"
inductive_cases [elim!]: "typecheck_constr CTriv t"
inductive_cases [elim!]: "typecheck_constr (CPair x y) t"

inductive de_morgan_dual :: "constr => constr => bool"
where "de_morgan_dual All Nothing"
    | "de_morgan_dual c1 c1' ==> de_morgan_dual c2 c2' ==> de_morgan_dual (And c1 c2) (Or c1' c2')"
    | "de_morgan_dual Nothing All"
    | "de_morgan_dual c1 c1' ==> de_morgan_dual c2 c2' ==> de_morgan_dual (Or c1 c2) (And c1' c2')"
    | "de_morgan_dual c c' ==> de_morgan_dual (CInL t1 t2 c) (Or (CInL t1 t2 c') (CInR t1 t2 All))"
    | "de_morgan_dual c c' ==> de_morgan_dual (CInR t1 t2 c) (Or (CInR t1 t2 c') (CInL t1 t2 All))"
    | "de_morgan_dual CTriv Nothing"
    | "de_morgan_dual c1 c1' ==> de_morgan_dual c2 c2' ==> 
          de_morgan_dual (CPair c1 c2) (Or (CPair c1' c2) (Or (CPair c1 c2') (CPair c1' c2')))"

inductive_cases [elim!]: "de_morgan_dual All t"
inductive_cases [elim!]: "de_morgan_dual (And x y) t"
inductive_cases [elim!]: "de_morgan_dual Nothing t"
inductive_cases [elim!]: "de_morgan_dual (Or x y) t"
inductive_cases [elim!]: "de_morgan_dual (CInL x y z) t"
inductive_cases [elim!]: "de_morgan_dual (CInR x y z) t"
inductive_cases [elim!]: "de_morgan_dual CTriv t"
inductive_cases [elim!]: "de_morgan_dual (CPair x y) t"

lemma [simp]: "typecheck_constr c t ==> de_morgan_dual c c' ==> typecheck_constr c' t"
by simp
sorry

inductive satisfies :: "expr => constr => bool"
where [simp]: "satisfies e All"
    | [simp]: "satisfies e c1 ==> satisfies e c2 ==> satisfies e (And c1 c2)"
    | [simp]: "satisfies e c1 ==> satisfies e (Or c1 c2)"
    | [simp]: "satisfies e c2 ==> satisfies e (Or c1 c2)"
    | [simp]: "satisfies e c ==> satisfies (InL t1 t2 e) (CInL t1 t2 c)"
    | [simp]: "satisfies e c ==> satisfies (InR t1 t2 e) (CInR t1 t2 c)"
    | [simp]: "satisfies Triv CTriv"
    | [simp]: "satisfies e1 c1 ==> satisfies e2 c2 ==> satisfies (Pair e1 e2) (CPair c1 c2)"

inductive_cases [elim!]: "satisfies e All"
inductive_cases [elim!]: "satisfies e (And x y)"
inductive_cases [elim!]: "satisfies e Nothing"
inductive_cases [elim!]: "satisfies e (Or x y)"
inductive_cases [elim!]: "satisfies e (CInL x y z)"
inductive_cases [elim!]: "satisfies e (CInR x y z)"
inductive_cases [elim!]: "satisfies e CTriv"
inductive_cases [elim!]: "satisfies e (CPair x y)"

lemma "de_morgan_dual c c' ==> satisfies e c' = (~ satisfies e c)"
proof auto
  assume "de_morgan_dual c c'"
     and "satisfies e c"
     and "satisfies e c'"
  thus False apply (induction c c' rule: de_morgan_dual.induct) by simp sorry
next
  assume "de_morgan_dual c c'"
     and "~ satisfies e c"
  thus "satisfies e c'" apply (induction c c' rule: de_morgan_dual.induct) by simp sorry
qed

definition totally_satisfied :: "constr => bool"
where "totally_satisfied c = (ALL v. satisfies v c)" (* TODO: not all, but ALL v : typecheck env v t *)

inductive types_from_pat :: "patn => type => type list => constr => bool"
where tpwld [simp]: "types_from_pat Wild t [] All"
    | tpvar [simp]: "types_from_pat PVar t [t] All"
    | tptrv [simp]: "types_from_pat PTriv Unit [] CTriv"
    | tppar [simp]: "types_from_pat p1 t1 ts1 c1 ==> types_from_pat p2 t2 ts2 c2 ==> 
          types_from_pat (PPair p1 p2) (Prod t1 t2) (ts1 @ ts2) (CPair c1 c2)"
    | tpinl [simp]: "types_from_pat p t1 ts c ==> types_from_pat (PInL p) (Sum t1 t2) ts (CInL t1 t2 c)"
    | tpinr [simp]: "types_from_pat p t2 ts c ==> types_from_pat (PInR p) (Sum t1 t2) ts (CInR t1 t2 c)"

inductive_cases [elim!]: "types_from_pat Wild t ts c"
inductive_cases [elim!]: "types_from_pat PVar t ts c"
inductive_cases [elim!]: "types_from_pat PTriv t ts c"
inductive_cases [elim!]: "types_from_pat (PPair p1 p2) t ts c"
inductive_cases [elim!]: "types_from_pat (PInL p) t ts c"
inductive_cases [elim!]: "types_from_pat (PInR p) t ts c"

lemma [simp]: "types_from_pat p t ts c ==> length ts = vars_count p"
by (induction p t ts c rule: types_from_pat.induct, simp_all)

inductive typecheck :: "(nat, type) assoc => expr => type => bool"
      and typecheck_rules :: "(nat, type) assoc => rule list => type => type => constr => bool"
      and typecheck_rule :: "(nat, type) assoc => rule => type => type => constr => bool"
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
    | tmch [simp]: "typecheck env e t1 ==> typecheck_rules env rs t1 t2 c ==> totally_satisfied c ==> typecheck env (Match e rs) t2" 
    | tnil [simp]: "typecheck_rules env [] t1 t2 Nothing"
    | tcns [simp]: "typecheck_rule env r t1 t2 c ==> typecheck_rules env rs t1 t2 cs ==> typecheck_rules env (r # rs) t1 t2 (Or c cs)"
    | trul [simp]: "types_from_pat p t1 ts c ==> typecheck (extend_env ts env) e t2 ==> typecheck_rule env (Rule p e) t1 t2 c"

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
inductive_cases [elim!]: "typecheck_rules e [] t t' c"
inductive_cases [elim!]: "typecheck_rules e (r # rs) t t' c"
inductive_cases [elim!]: "typecheck_rule e (Rule x y) t t' c"
                        
lemma [simp]: "typecheck env e t ==> typecheck (extend_at env n k) (incr_from n e) t"
  and [simp]: "typecheck_rules env rs t1 t2 c ==> typecheck_rules (extend_at env n k) (incr_from_rules n rs) t1 t2 c"
  and [simp]: "typecheck_rule env r t1 t2 c ==> typecheck_rule (extend_at env n k) (incr_from_rule n r) t1 t2 c"
proof (induction env e t and env rs t1 t2 c and env r t1 t2 c arbitrary: n and n and n rule: typecheck_typecheck_rules_typecheck_rule.inducts)
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
next case (tmch env e t1 rs t2 c)
  hence "typecheck (extend_at env n k) (incr_from n e) t1" by simp
  moreover from tmch have "typecheck_rules (extend_at env n k) (incr_from_rules n rs) t1 t2 c" by simp
  moreover from tmch have "totally_satisfied c" by simp
  ultimately show ?case by simp
next case tnil
  thus ?case by simp
next case tcns
  thus ?case by simp
next case (trul p t1 ts c env e t2)
  from trul have "vars_count p = length ts" by simp
  moreover from trul have "typecheck (extend_at (extend_env ts env) (n + vars_count p) k) (incr_from (n + vars_count p) e) t2" by simp
  ultimately have "typecheck (extend_env ts (extend_at env n k)) (incr_from (n + vars_count p) e) t2" by simp
  with trul show ?case by simp
qed

lemma [simp]: "typecheck env e t ==> typecheck (extend_env ts env) (incr_by (length ts) e) t"
by (induction ts, simp_all)        

lemma [simp]: "typecheck (extend_at env n k) e t ==> n ~: free_vars e ==> typecheck env (sub_from n e) t"
  and [simp]: "typecheck_rules (extend_at env n k) rs t1 t2 c ==> n ~: free_vars_rules rs ==> typecheck_rules env (sub_from_rules n rs) t1 t2 c"
  and [simp]: "typecheck_rule (extend_at env n k) r t1 t2 c ==> n ~: free_vars_rule r ==> typecheck_rule env (sub_from_rule n r) t1 t2 c"
proof (induction "extend_at env n k" e t and "extend_at env n k" rs t1 t2 c and "extend_at env n k" r t1 t2 c
       arbitrary: env n and env n and env n rule: typecheck_typecheck_rules_typecheck_rule.inducts)
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
next case (tmch e t1 rs t2 c)
  hence "typecheck_rules env (sub_from_rules n rs) t1 t2 c" by simp 
  moreover from tmch have "typecheck env (sub_from n e) t1" by simp
  moreover from tmch have "totally_satisfied c" by simp
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
  and [simp]: "typecheck_rules (extend env x t2) rs t1a t1b c ==> typecheck env eb t2 ==> typecheck_rules env (subst_rules rs eb x) t1a t1b c"
  and [simp]: "typecheck_rule (extend env x t2) r t1a t1b c ==> typecheck env eb t2 ==> typecheck_rule env (subst_rule r eb x) t1a t1b c"
proof (induction "extend env x t2" e t1 and "extend env x t2" rs t1a t1b c and "extend env x t2" r t1a t1b c
       arbitrary: env eb x and env eb x and env eb x rule: typecheck_typecheck_rules_typecheck_rule.inducts)
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
next case (tmch e t1 rs t2 c)
  hence "typecheck env (subst e eb x) t1" by simp
  moreover from tmch have "typecheck_rules env (subst_rules rs eb x) t1 t2 c" by simp
  moreover from tmch have "totally_satisfied c" by simp
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
