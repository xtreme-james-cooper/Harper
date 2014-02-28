theory Chapter13_4_Evaluation
imports Chapter13_3_PatternMatching
begin

inductive eval :: "expr => expr => bool"
      and eval_rules :: "expr => rule list => expr => bool"
where esuc [simp]: "eval n n' ==> eval (Succ n) (Succ n')"
    | eap1 [simp]: "eval e1 e1' ==> eval (Ap e1 e2) (Ap e1' e2)"
    | eap2 [simp]: "is_val e1 ==> eval e2 e2' ==> eval (Ap e1 e2) (Ap e1 e2')"
    | eap3 [simp]: "is_val e2 ==> eval (Ap (Lam t b) e2) (safe_subst b e2)"
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
    | ecs1 [simp]: "eval e e' ==> eval (Case e t rs) (Case e' t rs)"
    | ecs2 [simp]: "is_val e ==> eval_rules e rs e' ==> eval (Case e t rs) e'"
    | ers1 [simp]: "is_val e ==> matches s p e ==> eval_rules e (Rule p e2 # rs) (apply_subst s e2)"
    | ers2 [simp]: "is_val e ==> no_match e p ==> eval_rules e rs e' ==> eval_rules e (Rule p e2 # rs) e'"

theorem preservation: "eval e e' ==> typecheck env e t ==> typecheck env e' t"
    and "eval_rules e rs e' ==> typecheck_rules env rs t t' ==> typecheck env e t ==> typecheck env e' t'"
proof (induction e e' and e rs e' arbitrary: t env and t t' env rule: eval_eval_rules.inducts)
case esuc
  thus ?case by auto
next case (eap1 e1 e1' e2)
  hence "EX t2. typecheck env e1' (Arr t2 t) & typecheck env e2 t2" by auto
  thus ?case by auto
next case (eap2 e1 e2 e2')
  thus ?case by auto
next case eap3
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
next case (ecs1 e e' t1 rs)
  hence "typecheck env e t1 & typecheck_rules env rs t1 t" by auto
  moreover with ecs1 have "typecheck env e' t1" by simp
  ultimately show ?case by simp
next case ecs2
  thus ?case by auto
next case (ers1 e s p e2 rs)
  then obtain ts where "types_from_pat p t ts & typecheck (extend_env ts env) e2 t'" by auto
  moreover with ers1 have "typecheck_subst env s ts" by simp
  ultimately show ?case by simp
next case ers2
  thus ?case by auto
qed

lemma [simp]: "no_match v p ==> typecheck_rules env rs t t' ==> extract_constraints (Rule p e # rs) t c ==> 
                  is_val v ==> perfectly_satisfied t c ==> typecheck env v t ==> EX a. eval_rules v rs a"
proof (induction t c arbitrary: v p rs rule: perfectly_satisfied.induct)
case 1
  thus ?case by simp
next case (2 t t1 t2 c cs)
  thus ?case by simp sorry
next case (3 t t1 t2 c cs)
  thus ?case by simp sorry
next case (4 t cs)
  thus ?case by simp sorry
next case (5 t t1 t2 cs)
  thus ?case by simp sorry
next case 6
  thus ?case by simp sorry
next case 7
  thus ?case by simp sorry
qed

theorem progress: "typecheck env e t ==> env = empty_map ==> all_matches_complete e ==> is_val e | (EX e'. eval e e')"
    and "typecheck_rules env rs t1 t ==> extract_patterns rs c ==> is_val v ==> typecheck env v t1 ==> perfectly_satisfied t1 c ==> EX e'. eval_rules v rs e'"
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
next case (tcse env e t1 rs t2)
  thus ?case
  proof (cases "is_val e")
  case True
    thus ?thesis
    proof (cases rs)
    case Nil
      with tcse show ?thesis by auto
    next case (Cons r rs')
      from tcse have "EX cs. all_matches_complete e & extract_patterns rs cs & perfectly_satisfied t1 cs" by auto
      then obtain cs where "all_matches_complete e & extract_patterns rs cs & perfectly_satisfied t1 cs" by auto
      with Cons have "all_matches_complete e & (EX c1 c2. cs = c1 # c2 & extract_pattern r c1 & extract_patterns rs' c2) & perfectly_satisfied t1 cs" by auto
      thus ?thesis 
      proof auto
        fix c1 c2
        assume "all_matches_complete e"
           and "perfectly_satisfied t1 (c1 # c2)"
           and "extract_pattern r c1"
           and "extract_patterns rs' c2"
        moreover from tcse True Cons have "extract_patterns (r # rs') (c1 # c2) ==> perfectly_satisfied t1 (c1 # c2) ==> EX a. eval_rules e (r # rs') a" by simp
        ultimately obtain a where "eval_rules e (r # rs') a" by auto
        with True have "eval (Case e t1 (r # rs')) a" by simp
        with Cons show "EX a. (eval (Case e t1 rs)) a" by auto      
      qed
    qed
  next case False
    with tcse have "EX a. eval e a" by auto
    then obtain a where "eval e a" by auto
    hence "eval (Case e t1 rs) (Case a t1 rs)" by simp
    thus ?thesis by auto
  qed
next case tnil
  thus ?case by auto
next case (tcns env r t1 t2 rs)
  thus ?case
  proof (cases r)
  case (Rule p e)
    from tcns Rule obtain ts where "types_from_pat p t1 ts & typecheck (extend_env ts env) e t2" by auto
    moreover from tcns have "types_from_pat p t1 ts ==> (EX s. typecheck_subst env s ts & matches s p v) | no_match v p" by simp
    ultimately have X: "(EX s. typecheck_subst env s ts & matches s p v) | no_match v p" by simp
    thus ?thesis
    proof (cases "EX s. matches s p v")
    case False
      with X have Y: "no_match v p" by simp
      with tcns Rule have "EX a. eval_rules v rs a" by simp
      then obtain a where "eval_rules v rs a" by auto
      with Y tcns have "eval_rules v (Rule p e # rs) a" by simp
      with Rule show ?thesis by auto
    next case True
      with X obtain s where "matches s p v" by auto
      with tcns have "eval_rules v (Rule p e # rs) (apply_subst s e)" by simp
      with Rule show ?thesis by auto
    qed
  qed
next case trul
  thus ?case by simp
qed 

end
