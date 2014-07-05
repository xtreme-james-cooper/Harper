theory Chapter05_06
imports Chapter04
begin

primrec is_val :: "expr => bool"
where "is_val (Var v) = False"
    | "is_val (Num x) = True"
    | "is_val (Str s) = True"
    | "is_val (Plus e1 e2) = False"
    | "is_val (Times e1 e2) = False"
    | "is_val (Cat e1 e2) = False"
    | "is_val (Len e) = False"
    | "is_val (Let e1 e2) = False"

inductive eval :: "expr => expr => bool"
where eval_plus_1 [simp]: "eval (Plus (Num n1) (Num n2)) (Num (n1 + n2))"
    | eval_plus_2 [simp]: "eval e1 e1' ==> eval (Plus e1 e2) (Plus e1' e2)"
    | eval_plus_3 [simp]: "is_val e1 ==> eval e2 e2' ==> eval (Plus e1 e2) (Plus e1 e2')"
    | eval_times_1 [simp]: "eval (Times (Num n1) (Num n2)) (Num (n1 * n2))"
    | eval_times_2 [simp]: "eval e1 e1' ==> eval (Times e1 e2) (Times e1' e2)"
    | eval_times_3 [simp]: "is_val e1 ==> eval e2 e2' ==> eval (Times e1 e2) (Times e1 e2')"
    | eval_cat_1 [simp]: "eval (Cat (Str n1) (Str n2)) (Str (n1 @ n2))"
    | eval_cat_2 [simp]: "eval e1 e1' ==> eval (Cat e1 e2) (Cat e1' e2)"
    | eval_cat_3 [simp]: "is_val e1 ==> eval e2 e2' ==> eval (Cat e1 e2) (Cat e1 e2')"
    | eval_len_1 [simp]: "eval (Len (Str n1)) (Num (int (length n1)))"
    | eval_len_2 [simp]: "eval e1 e1' ==> eval (Len e1) (Len e1')"
    | eval_let_1 [simp]: "is_val e1 ==> eval (Let e1 e2) (subst e1 e2)"
    | eval_let_2 [simp]: "eval e1 e1' ==> eval (Let e1 e2) (Let e1' e2)"

lemma canonical_num: "is_val e ==> typecheck gam e NumType ==> EX n. e = Num n"
by (induction e, auto)

lemma canonical_str: "is_val e ==> typecheck gam e StrType ==> EX n. e = Str n"
by (induction e, auto)

theorem preservation: "eval e e' ==> typecheck gam e t ==> typecheck gam e' t"
proof (induction e e' arbitrary: t rule: eval.induct)
case eval_plus_1 
  thus ?case by auto
next case eval_plus_2 
  thus ?case by auto
next case eval_plus_3 
  thus ?case by auto
next case eval_times_1 
  thus ?case by auto
next case eval_times_2 
  thus ?case by auto
next case eval_times_3 
  thus ?case by auto
next case eval_cat_1 
  thus ?case by auto
next case eval_cat_2 
  thus ?case by auto
next case  eval_cat_3 
  thus ?case by auto
next case eval_len_1 
  thus ?case by auto
next case eval_len_2 
  thus ?case by auto
next case eval_let_1
  thus ?case by auto
next case (eval_let_2 e1 e1' e2)
  from eval_let_2 obtain t2 where T2: "typecheck gam e1' t2 & 
                                       typecheck (extend gam t2) e2 t" by auto
  with eval_let_2 have "typecheck gam e1' t2" by simp
  with T2 show ?case by simp
qed

theorem progress: "typecheck gam e t ==> gam = empty_env ==> is_val e | (EX e'. eval e e')"
proof (induction gam e t rule: typecheck.induct)
case tc_var
  thus ?case by simp
next case tc_str
  thus ?case by simp
next case tc_num
  thus ?case by simp
next case (tc_plus gam e1 e2)
  thus ?case
  proof (cases "is_val e1")
  case True note T = True 
    thus ?thesis
    proof (cases "is_val e2")
    case True
      with tc_plus canonical_num obtain n2 where N2: "e2 = Num n2" by auto
      from tc_plus T canonical_num obtain n1 where "e1 = Num n1" by auto
      with N2 have "eval (Plus e1 e2) (Num (n1 + n2))" by simp
      thus ?thesis by auto
    next case False
      with tc_plus obtain a where "eval e2 a" by auto
      with True have "eval (Plus e1 e2) (Plus e1 a)" by simp
      thus ?thesis by auto
    qed
  next case False
    with tc_plus obtain a where "eval e1 a" by auto
    hence "eval (Plus e1 e2) (Plus a e2)" by simp
    thus ?thesis by auto
  qed
next case (tc_times gam e1 e2)
  thus ?case
  proof (cases "is_val e1")
  case True note T = True 
    thus ?thesis
    proof (cases "is_val e2")
    case True
      with tc_times canonical_num obtain n2 where N2: "e2 = Num n2" by auto
      from tc_times T canonical_num obtain n1 where "e1 = Num n1" by auto
      with N2 have "eval (Times e1 e2) (Num (n1 * n2))" by simp
      thus ?thesis by auto
    next case False
      with tc_times obtain a where "eval e2 a" by auto
      with True have "eval (Times e1 e2) (Times e1 a)" by simp
      thus ?thesis by auto
    qed
  next case False
    with tc_times obtain a where "eval e1 a" by auto
    hence "eval (Times e1 e2) (Times a e2)" by simp
    thus ?thesis by auto
  qed
next case (tc_cat gam e1 e2)
  thus ?case
  proof (cases "is_val e1")
  case True note T = True 
    thus ?thesis
    proof (cases "is_val e2")
    case True
      with tc_cat canonical_str obtain n2 where N2: "e2 = Str n2" by auto
      from tc_cat T canonical_str obtain n1 where "e1 = Str n1" by auto
      with N2 have "eval (Cat e1 e2) (Str (n1 @ n2))" by simp
      thus ?thesis by auto
    next case False
      with tc_cat obtain a where "eval e2 a" by auto
      with True have "eval (Cat e1 e2) (Cat e1 a)" by simp
      thus ?thesis by auto
    qed
  next case False
    with tc_cat obtain a where "eval e1 a" by auto
    hence "eval (Cat e1 e2) (Cat a e2)" by simp
    thus ?thesis by auto
  qed
next case (tc_len gam e)
  thus ?case
  proof (cases "is_val e")
  case True 
    with tc_len canonical_str obtain s where "e = Str s" by auto
    hence "eval (Len e) (Num (int (length s)))" by simp
    thus ?thesis by auto
  next case False
    with tc_len obtain a where "eval e a" by auto
    hence "eval (Len e) (Len a)" by simp
    thus ?thesis by auto
  qed
next case (tc_let gam e1 t1 e2 t2)
  thus ?case
  proof (cases "is_val e1")
  case True 
    hence "eval (Let e1 e2) (subst e1 e2)" by simp
    thus ?thesis by auto
  next case False
    with tc_let obtain a where "eval e1 a" by auto
    hence "eval (Let e1 e2) (Let a e2)" by simp
    thus ?thesis by auto
  qed
qed

end
