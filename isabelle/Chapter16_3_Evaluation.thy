theory Chapter16_3_Evaluation
imports Chapter16_2_Typechecking
begin

fun is_val :: "expr => bool"
where "is_val (Var v) = False"
    | "is_val (Lam t b) = True"
    | "is_val (Ap e1 e2) = False"
    | "is_val (Fix t b) = False"
    | "is_val Triv = True"
    | "is_val (Pair e1 e2) = (is_val e1 & is_val e2)"
    | "is_val (ProjL e) = False"
    | "is_val (ProjR e) = False"
    | "is_val (Abort t e) = False"
    | "is_val (InL t t' e) = is_val e"
    | "is_val (InR t t' e) = is_val e"
    | "is_val (Case e el er) = False"
    | "is_val (Fold t e) = is_val e"
    | "is_val (Unfold e) = False"

lemma canonical_arr: "typecheck env e (Arr t1 t2) ==> is_val e ==> (EX v. e = Lam t1 v & typecheck (extend_at env 0 t1) v t2)"
by (induction e, auto)

lemma canonical_unit: "typecheck env e Unit ==> is_val e ==> e = Triv"
by (induction e, auto)

lemma canonical_prod: "typecheck env e (Prod t1 t2) ==> is_val e ==> (EX e1 e2. e = Pair e1 e2 & typecheck env e1 t1 & typecheck env e2 t2 & is_val e1 & is_val e2)"
by (induction e, auto)

lemma canonical_void: "typecheck env e Void ==> ~ is_val e"
by (induction e, auto)

lemma canonical_sum: "typecheck env e (Sum t1 t2) ==> is_val e ==> 
      (EX e'. e = InL t1 t2 e' & is_val e' & typecheck env e' t1) | (EX e'. e = InR t1 t2 e' & is_val e' & typecheck env e' t2)"
by (induction e, auto)

lemma canonical_rec: "typecheck env e (Rec t) ==> is_val e ==> EX e'. e = Fold t e' & is_val e'"
by (induction e, auto)

inductive eval :: "expr => expr => bool"
where eap1 [simp]: "eval e1 e1' ==> eval (Ap e1 e2) (Ap e1' e2)"
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
    | ecs1 [simp]: "eval e e' ==> eval (Case e el er) (Case e' el er)"
    | ecs2 [simp]: "is_val e ==> eval (Case (InL t t' e) el er) (safe_subst el e)"
    | ecs3 [simp]: "is_val e ==> eval (Case (InR t t' e) el er) (safe_subst er e)"
    | efld [simp]: "eval e e' ==> eval (Fold t e) (Fold t e')"
    | euf1 [simp]: "eval e e' ==> eval (Unfold e) (Unfold e')"
    | euf2 [simp]: "is_val e ==> eval (Unfold (Fold t e)) e"

theorem preservation: "eval e e' ==> typecheck env e t ==> typecheck env e' t"
proof (induction e e' arbitrary: t env rule: eval.inducts)
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
next case (ecs1 e e' el er)
  then obtain t1 t2 where T: "typecheck env e (Sum t1 t2) & 
                            typecheck (extend_at env 0 t1) el t & 
                            typecheck (extend_at env 0 t2) er t" by auto
  with ecs1 have "typecheck env e' (Sum t1 t2)" by simp
  with T show ?case by simp
next case ecs2
  thus ?case by auto
next case ecs3
  thus ?case by auto
next case efld
  thus ?case by auto
next case euf1
  thus ?case by auto
next case euf2
  thus ?case by auto
qed

theorem progress: "typecheck env e t ==> env = empty_map ==> is_val e | (EX e'. eval e e')"
proof (induction env e t arbitrary: rule: typecheck.inducts)
case tvar
  thus ?case by auto
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
next case (tcse env e t1 t2 el t er)
  thus ?case
  proof (cases "is_val e")
  case True
    with tcse have "(EX e'. e = InL t1 t2 e' & is_val e' & typecheck env e' t1) | (EX e'. e = InR t1 t2 e' & is_val e' & typecheck env e' t2)" by (simp add: canonical_sum)
    thus ?thesis
    proof (cases "EX e'. e = InL t1 t2 e'", auto)
      fix e'
      assume "is_val e'" 
      hence "EX x. eval (Case (InL t1 t2 e') el er) (safe_subst el e')" by simp
      thus "EX x. eval (Case (InL t1 t2 e') el er) x" by auto
    next
      fix e'
      assume "is_val e'" 
      hence "EX x. eval (Case (InR t1 t2 e') el er) (safe_subst er e')" by simp
      thus "EX x. eval (Case (InR t1 t2 e') el er) x" by auto
    qed
  next case False
    with tcse have "EX a. eval e a" by simp
    thus ?thesis
    proof auto
      fix a
      assume "eval e a"
      hence "eval (Case e el er) (Case a el er)" by simp
      thus "EX x. eval (Case e el er) x" by auto
    qed
  qed
next case (tfld env e t)
  thus ?case
  proof (cases "is_val e", auto)
    fix a
    assume "eval e a"
    hence "eval (Fold t e) (Fold t a)" by auto
    thus "EX a. eval (Fold t e) a" by auto
  qed
next case (tufd env e t)
  thus ?case
  proof (cases "is_val e")
  case True
    with tufd have "EX e'. e = Fold t e' & is_val e'" by (simp add: canonical_rec)
    then obtain e' where E': "e = Fold t e' & is_val e'" by auto
    hence "eval (Unfold (Fold t e')) e'" by simp
    hence "EX a. eval (Unfold (Fold t e')) a" by auto
    with E' show ?thesis by auto
  next case False
    with tufd obtain a where "eval e a" by auto
    hence "eval (Unfold e) (Unfold a)" by auto
    thus ?thesis by auto
  qed
qed 

end
