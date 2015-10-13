theory Chapter05_06
imports Chapter04
begin

primrec is_val :: "expr \<Rightarrow> bool" where 
  "is_val (Var v) = False"
| "is_val (Num x) = True"
| "is_val (Str s) = True"
| "is_val (Plus e1 e2) = False"
| "is_val (Times e1 e2) = False"
| "is_val (Cat e1 e2) = False"
| "is_val (Len e) = False"
| "is_val (Let e1 e2) = False"

inductive eval :: "expr \<Rightarrow> expr \<Rightarrow> bool" where 
  eval_plus_1 [simp]: "eval (Plus (Num n1) (Num n2)) (Num (n1 + n2))"
| eval_plus_2 [simp]: "eval e1 e1' \<Longrightarrow> eval (Plus e1 e2) (Plus e1' e2)"
| eval_plus_3 [simp]: "is_val e1 \<Longrightarrow> eval e2 e2' \<Longrightarrow> eval (Plus e1 e2) (Plus e1 e2')"
| eval_times_1 [simp]: "eval (Times (Num n1) (Num n2)) (Num (n1 * n2))"
| eval_times_2 [simp]: "eval e1 e1' \<Longrightarrow> eval (Times e1 e2) (Times e1' e2)"
| eval_times_3 [simp]: "is_val e1 \<Longrightarrow> eval e2 e2' \<Longrightarrow> eval (Times e1 e2) (Times e1 e2')"
| eval_cat_1 [simp]: "eval (Cat (Str n1) (Str n2)) (Str (n1 @ n2))"
| eval_cat_2 [simp]: "eval e1 e1' \<Longrightarrow> eval (Cat e1 e2) (Cat e1' e2)"
| eval_cat_3 [simp]: "is_val e1 \<Longrightarrow> eval e2 e2' \<Longrightarrow> eval (Cat e1 e2) (Cat e1 e2')"
| eval_len_1 [simp]: "eval (Len (Str n1)) (Num (int (length n1)))"
| eval_len_2 [simp]: "eval e1 e1' \<Longrightarrow> eval (Len e1) (Len e1')"
| eval_let_1 [simp]: "is_val e1 \<Longrightarrow> eval (Let e1 e2) (subst e1 first e2)"
| eval_let_2 [simp]: "eval e1 e1' \<Longrightarrow> eval (Let e1 e2) (Let e1' e2)"

lemma canonical_num: "is_val e \<Longrightarrow> typecheck gam e NumType \<Longrightarrow> \<exists>n. e = Num n"
  by (induction e) auto

lemma canonical_str: "is_val e \<Longrightarrow> typecheck gam e StrType \<Longrightarrow> \<exists>n. e = Str n"
  by (induction e) auto

theorem preservation: "eval e e' \<Longrightarrow> typecheck gam e t \<Longrightarrow> typecheck gam e' t"
  by (induction e e' arbitrary: t rule: eval.induct) fastforce+

theorem progress: "typecheck gam e t \<Longrightarrow> gam = empty_env \<Longrightarrow> is_val e \<or> (\<exists>e'. eval e e')"
  proof (induction gam e t rule: typecheck.induct)
  case tc_var
    thus ?case by simp
  next case tc_str
    thus ?case by simp
  next case tc_num
    thus ?case by simp
  next case tc_plus
    thus ?case by (metis eval_plus_1 eval_plus_2 eval_plus_3 canonical_num)
  next case tc_times
    thus ?case by (metis eval_times_1 eval_times_2 eval_times_3 canonical_num)
  next case tc_cat
    thus ?case by (metis eval_cat_1 eval_cat_2 eval_cat_3 canonical_str)
  next case tc_len
    thus ?case by (metis eval_len_1 eval_len_2 canonical_str)
  next case tc_let
    thus ?case by (metis eval_let_1 eval_let_2)
  qed

end
