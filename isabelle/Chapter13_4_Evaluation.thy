theory Chapter13_4_Evaluation
imports Chapter13_3_PatternMatching
begin

inductive eval :: "expr => expr => bool"
where esuc [simp]: "eval n n' ==> eval (Succ n) (Succ n')"
    | eap1 [simp]: "eval e1 e1' ==> eval (Ap e1 e2) (Ap e1' e2)"
    | eap2 [simp]: "is_val e1 ==> eval e2 e2' ==> eval (Ap e1 e2) (Ap e1 e2')"
    | eap3 [simp]: "is_val e2 ==> eval (Ap (Lam t b) e2) (safe_subst b e2)"
    | eiz1 [simp]: "eval e e' ==> eval (IsZ e0 e1 e) (IsZ e0 e1 e')"
    | eiz2 [simp]: "eval (IsZ e0 e1 Zero) e0"
    | eiz3 [simp]: "is_val e ==> eval (IsZ e0 e1 (Succ e)) (safe_subst e1 e)"
    | efix [simp]: "eval (Fix t b) (safe_subst b (Fix t b))"
    | epa1 [simp]: "eval e1 e1' ==> eval (Pair e1 e2) (Pair e1' e2)"
    | epa2 [simp]: "is_val e1 ==> eval e2 e2' ==> eval (Pair e1 e2) (Pair e1 e2')"
    | epl1 [simp]: "eval e e' ==> eval (ProjL e) (ProjL e')"
    | epl2 [simp]: "is_val e1 ==> is_val e2 ==> eval (ProjL (Pair e1 e2)) e1"
    | epr1 [simp]: "eval e e' ==> eval (ProjR e) (ProjR e')"
    | epr2 [simp]: "is_val e1 ==> is_val e2 ==> eval (ProjR (Pair e1 e2)) e2"
    | eabt [simp]: "eval e e' ==> eval (Abort t e) (Abort t e')"
    | einl [simp]: "eval e e' ==> eval (InL t t' e) (InL t t' e')"
    | einr [simp]: "eval e e' ==> eval (InR t t' e) (InR t t' e')"
    | emt1 [simp]: "eval e e' ==> eval (Match e t rs) (Match e' t rs)"
    | emt2 [simp]: "is_val e ==> matches s p e ==> eval (Match e t (Rule p e2 # rs)) (apply_subst s e2)"
    | emt3 [simp]: "is_val e ==> no_match e p ==> eval (Match e t rs) e' ==> eval (Match e t (Rule p e2 # rs)) e'"

theorem preservation: "eval e e' ==> typecheck env e t ==> typecheck env e' t"
proof (induction e e' arbitrary: t env rule: eval.induct)
case esuc
  thus ?case by auto
next case (eap1 e1 e1' e2)
  hence "EX t2. typecheck env e1' (Arr t2 t) & typecheck env e2 t2" by auto
  thus ?case by auto
next case (eap2 e1 e2 e2')
  thus ?case by auto
next case eap3
  thus ?case by auto
next case eiz1
  thus ?case by auto
next case eiz2
  thus ?case by auto
next case eiz3
  thus ?case by auto
next case efix
  thus ?case by auto
next case epa1
  thus ?case by auto
next case epa2
  thus ?case by auto
next case (epl1 e e')
  hence "!!t2. typecheck env e (Prod t t2) ==> typecheck env e' (Prod t t2)" by simp
  with epl1 have "EX t2. typecheck env e' (Prod t t2)" by auto
  thus ?case by auto
next case epl2
  thus ?case by auto
next case (epr1 e e')
  hence "!!t1. typecheck env e (Prod t1 t) ==> typecheck env e' (Prod t1 t)" by simp
  with epr1 have "EX t1. typecheck env e' (Prod t1 t)" by auto
  thus ?case by auto
next case epr2
  thus ?case by auto
next case eabt
  thus ?case by auto
next case einl
  thus ?case by auto
next case einr
  thus ?case by auto
next case (emt1 e e' t1 rs)
  hence "typecheck env e t1 & typecheck_rules env rs t1 t" by auto
  moreover with emt1 have "typecheck env e' t1" by simp
  ultimately show ?case by simp
next case (emt2 e s p t1 e' rs)
  thus ?case
  proof auto
    fix ts
    assume W: "is_val e" 
       and V: "matches s p e" 
       and Z: "typecheck env e t1" 
       and Y: "types_from_pat p t1 ts"
       and X: "typecheck (extend_env ts env) e' t" 
    have "types_from_pat p t1 ts ==> typecheck env e t1 ==> is_val e ==> (EX s. typecheck_subst env s ts & matches s p e) | no_match e p" by simp
    with Y Z W V obtain sa where "typecheck_subst env sa ts & matches sa p e" by auto
    moreover with V have "sa = s" by auto 
    ultimately have "typecheck_subst env s ts" by simp
    with X show "typecheck env (apply_subst s e') t" by simp
  qed
next case emt3
  thus ?case by auto
qed

theorem progress: "typecheck env e t ==> env = empty_map ==> all_matches_complete e ==> is_val e | (EX e'. eval e e')"
    and "typecheck_rules env rs t1 t ==> extract_constraints rs t1 c ==> is_val v ==> typecheck env v t1 ==> perfectly_satisfied c ==> EX e'. eval (Match v t1 rs) e'"
    and "typecheck_rule env r t1 t ==> True"
proof (induction env e t and env rs t1 t arbitrary: and v c rule: typecheck_typecheck_rules_typecheck_rule.inducts)
case tvar
  thus ?case by auto
next case tzer
  thus ?case by simp
next case (tsuc env n)
  thus ?case 
  proof (cases "is_val n", auto)
    fix x
    assume "eval n x"
    hence "eval (Succ n) (Succ x)" by simp
    thus "EX y. eval (Succ n) y " by auto
  qed
next case (trec env e e0 t e1)
  thus ?case
  proof (cases "is_val e")
  case True
    have "EX x. eval (IsZ e0 e1 e) x"
    proof (cases "e = Zero")
    case True
      def e0' == e0
      have "eval (IsZ e0 e1 Zero) e0'" by (simp add: e0'_def)
      with True show ?thesis by auto
    next case False
      from trec True have "e = Zero | (EX v. typecheck env v Nat & is_val v & e = Succ v)" by (simp add: canonical_nat)
      with False have "EX v. typecheck env v Nat & is_val v & e = Succ v" by simp
      thus ?thesis
      proof auto
        fix v
        assume "is_val v"
        hence "eval (IsZ e0 e1 (Succ v)) (safe_subst e1 v)" by simp
        thus "EX x. eval (IsZ e0 e1 (Succ v)) x" by auto
      qed
    qed
    thus ?thesis by simp
  next case False
    with trec have "\<exists>a. eval e a" by auto
    thus ?thesis
    proof auto
      fix a
      assume "eval e a"
      hence "eval (IsZ e0 e1 e) (IsZ e0 e1 a)" by simp
      thus "EX x. eval (IsZ e0 e1 e) x" by auto
    qed
  qed
next case tlam
  thus ?case by simp
next case (tapp env e1 t2 t e2)
  show ?case
  proof (cases "is_val e1")
  case True
    with tapp have "EX v. e1 = Lam t2 v & typecheck (extend_at env 0 t2) v t" by (simp add: canonical_arr)
    hence e1_is_lam: "EX v. e1 = Lam t2 v" by auto
    thus ?thesis 
    proof (cases "is_val e2")
    case True
      with e1_is_lam show ?thesis
      proof auto
        fix v
        assume "is_val e2"
        hence "eval (Ap (Lam t2 v) e2) (safe_subst v e2)" by simp
        thus "EX x. eval (Ap (Lam t2 v) e2) x" by auto
      qed
    next case False
      with tapp have "\<exists>a. eval e2 a" by auto
      thus ?thesis
      proof auto
        fix a
        assume "eval e2 a"
        moreover from True have "is_val e1" by simp
        ultimately have "eval (Ap e1 e2) (Ap e1 a)" by simp
        thus "EX x. eval (Ap e1 e2) x" by auto
      qed
    qed
  next case False
    with tapp have "\<exists>a. eval e1 a" by auto
    thus ?thesis
    proof auto
      fix a
      assume "eval e1 a"
      hence "eval (Ap e1 e2) (Ap a e2)" by simp
      thus "EX x. eval (Ap e1 e2) x" by auto
    qed
  qed
next case (tfix env t b)
  def b' == "safe_subst b (Fix t b)"
  have "eval (Fix t b) b'" by (simp add: b'_def)
  thus ?case by auto
next case ttrv
  thus ?case by simp
next case (tpar env e1 t1 e2 t2)
  thus ?case
  proof (cases "is_val e1")
  case True
    hence X: "is_val e1" by simp
    thus ?thesis
    proof (cases "is_val e2")
    case True
      with X show ?thesis by simp  
    next case False
      with tpar have "EX a. eval e2 a" by auto
      hence "EX a. eval (Pair e1 e2) a"
      proof auto
        fix e2'
        assume "eval e2 e2'"
        with True have "eval (Pair e1 e2) (Pair e1 e2')" by simp
        thus "EX a. eval (Pair e1 e2) a" by auto
      qed
      thus ?thesis by simp  
    qed
  next case False
    with tpar have "EX a. eval e1 a" by auto
    hence "EX a. eval (Pair e1 e2) a"
    proof auto
      fix e1'
      assume "eval e1 e1'"
      hence "eval (Pair e1 e2) (Pair e1' e2)" by simp
      thus "EX a. eval (Pair e1 e2) a" by auto
    qed
    with False show ?thesis by simp
  qed
next case (tprl env e t1 t2)
  thus ?case
  proof (cases "is_val e")
  case True
    with tprl have "EX e1 e2. e = Pair e1 e2 & typecheck env e1 t1 & typecheck env e2 t2 & is_val e1 & is_val e2" by (simp add: canonical_prod)
    thus ?thesis
    proof auto
      fix e1 e2
      assume "is_val e1"
         and "is_val e2"
      hence "eval (ProjL (Pair e1 e2)) e1" by simp
      thus "EX a. eval (ProjL (Pair e1 e2)) a" by auto
    qed
  next case False
    with tprl have "EX a. eval e a" by auto
    thus ?thesis
    proof auto
      fix a
      assume "eval e a"
      hence "eval (ProjL e) (ProjL a)" by simp
      thus "EX a. eval (ProjL e) a" by auto
    qed
  qed
next case (tprr env e t1 t2)
  thus ?case
  proof (cases "is_val e")
  case True
    with tprr have "EX e1 e2. e = Pair e1 e2 & typecheck env e1 t1 & typecheck env e2 t2 & is_val e1 & is_val e2" by (simp add: canonical_prod)
    thus ?thesis
    proof auto
      fix e1 e2
      assume "is_val e1"
         and "is_val e2"
      hence "eval (ProjR (Pair e1 e2)) e2" by simp
      thus "EX a. eval (ProjR (Pair e1 e2)) a" by auto
    qed
  next case False
    with tprr have "EX a. eval e a" by auto
    thus ?thesis
    proof auto
      fix a
      assume "eval e a"
      hence "eval (ProjR e) (ProjR a)" by simp
      thus "EX a. eval (ProjR e) a" by auto
    qed
  qed
next case (tabt env e t)
  thus ?case
  proof (cases "is_val e", auto simp add: canonical_void)
    fix x
    assume "eval e x"
    hence "eval (Abort t e) (Abort t x)" by simp
    thus "EX x. eval (Abort t e) x" by auto
  qed
next case (tinl env e t1 t2)
  thus ?case 
  proof (cases "is_val e", auto)
    fix x
    assume "eval e x"
    hence "eval (InL t1 t2 e) (InL t1 t2 x)" by simp
    thus "EX y. eval (InL t1 t2 e) y " by auto
  qed
next case (tinr env e t2 t1)
  thus ?case 
  proof (cases "is_val e", auto)
    fix x
    assume "eval e x"
    hence "eval (InR t1 t2 e) (InR t1 t2 x)" by simp
    thus "EX y. eval (InR t1 t2 e) y " by auto
  qed
next case (tmch env e t1 rs t2)
  thus ?case
  proof (cases "is_val e")
  case True
    from tmch have "EX cs. extract_constraints rs t1 cs & perfectly_satisfied cs" by auto
    with True tmch show ?thesis by auto sorry
  next case False
    with tmch have "EX a. eval e a" by auto
    thus ?thesis
    proof auto
      fix a
      assume "eval e a"
      hence "eval (Match e t1 rs) (Match a t1 rs)" by simp
      thus "EX x. eval (Match e t1 rs) x" by auto
    qed
  qed
next case tnil
  thus ?case by auto
next case (tcns env r t1 t2 rs)
  thus ?case
  proof (cases r)
  case (Rule p e2)
    moreover from tcns Rule have "EX c1 c2. c = c1 # c2 & extract_constraint_rule (Rule p e2) t1 c1 & extract_constraints rs t1 c2" by auto
    moreover from tcns Rule have "EX ts. types_from_pat p t1 ts & typecheck (extend_env ts env) e2 t2" by auto
    ultimately show ?thesis by simp sorry
  qed
next case trul
  thus ?case by simp
qed 

end
