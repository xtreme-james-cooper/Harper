theory Chapter08_3_Evaluation
imports Chapter08_2_Typechecking
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
    | "is_val (Lam t e) = True"
    | "is_val (Appl e1 e2) = False"

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
    | eval_appl_1 [simp]: "eval e1 e1' ==> eval (Appl e1 e2) (Appl e1' e2)"
    | eval_appl_2 [simp]: "is_val e1 ==> eval e2 e2' ==> eval (Appl e1 e2) (Appl e1 e2')"
    | eval_appl_3 [simp]: "is_val e2 ==> eval (Appl (Lam t2 e1) e2) (subst e2 e1)"

lemma canonical_num: "is_val e ==> typecheck gam e NumType ==> EX n. e = Num n"
by (induction e, auto)

lemma canonical_str: "is_val e ==> typecheck gam e StrType ==> EX n. e = Str n"
by (induction e, auto)

lemma canonical_arrow: "is_val e ==> typecheck gam e (Arrow t1 t2) ==> 
              EX e'. e = Lam t1 e' & typecheck (extend gam t1) e' t2"
by (induction e, auto)

theorem preservation: "eval e e' ==> typecheck gam e t ==> typecheck gam e' t"
by (induction e e' arbitrary: t rule: eval.induct, fastforce+)

theorem progress: "typecheck gam e t ==> gam = empty_env ==> is_val e | (EX e'. eval e e')"
proof (induction gam e t rule: typecheck.induct)
case tc_var
  thus ?case by simp
next case tc_str
  thus ?case by simp
next case tc_num
  thus ?case by simp
next case (tc_plus gam e1 e2)
  thus ?case by (metis eval_plus_1 eval_plus_2 eval_plus_3 canonical_num)
next case (tc_times gam e1 e2)
  thus ?case by (metis eval_times_1 eval_times_2 eval_times_3 canonical_num)
next case (tc_cat gam e1 e2)
  thus ?case by (metis eval_cat_1 eval_cat_2 eval_cat_3 canonical_str)
next case (tc_len gam e)
  thus ?case by (metis eval_len_1 eval_len_2 canonical_str)
next case (tc_let gam e1 t1 e2 t2)
  thus ?case by (metis eval_let_1 eval_let_2)
next case (tc_lam gam t1 e t2)
  thus ?case by simp
next case (tc_appl gam e1 t2 t e2)
  thus ?case by (metis eval_appl_1 eval_appl_2 eval_appl_3 canonical_arrow)
qed

end
