theory Chapter18_3_Evaluation
imports Chapter18_2_Typechecking
begin

primrec is_val :: "expr => bool"
where "is_val (Var v) = False"
    | "is_val (Num n) = True"
    | "is_val Zero = False"
    | "is_val (Succ e) = False"
    | "is_val (IsZ et e0 es) = False"
    | "is_val (Lam e) = True"
    | "is_val (Appl e1 e2) = False"
    | "is_val (Fix e) = False"

inductive eval :: "expr => expr => bool"
and error :: "expr => bool"
where eval_zero [simp]: "eval Zero (Num 0)"
    | eval_suc_1 [simp]: "eval e e' ==> eval (Succ e) (Succ e')"
    | eval_suc_2 [simp]: "error d ==> error (Succ d)"
    | eval_suc_3 [simp]: "eval (Succ (Num n)) (Num (Suc n))"
    | eval_suc_4 [simp]: "error (Succ (Lam e)) "
    | eval_isz_1 [simp]: "eval et et' ==> eval (IsZ et e0 es) (IsZ et' e0 es)"
    | eval_isz_2 [simp]: "error d ==> error (IsZ d e0 es)"
    | eval_isz_3 [simp]: "eval (IsZ (Num 0) e0 es) e0"
    | eval_isz_4 [simp]: "eval (IsZ (Num (Suc et)) e0 es) (subst (Num et) es)"
    | eval_isz_5 [simp]: "error (IsZ (Lam et) e0 es)"
    | eval_appl_1 [simp]: "eval e1 e1' ==> eval (Appl e1 e2) (Appl e1' e2)"
    | eval_appl_2 [simp]: "error e1 ==> error (Appl e1 e2)"
    | eval_appl_3 [simp]: "error (Appl (Num e1) e2)"
    | eval_appl_4 [simp]: "eval (Appl (Lam e1) e2) (subst e2 e1)"
    | eval_fix [simp]: "eval (Fix e) (subst (Fix e) e)"

theorem preservation: "eval e e' ==> is_ok del e ==> is_ok del e'" and "error f ==> True"
by (induction e e' and f arbitrary: del rule: eval_error.inducts, fastforce+)

theorem progress: "is_ok del e ==> del = empty_env ==> is_val e | (EX e'. eval e e') | error e"
proof (induction e arbitrary: del)
case Var
  thus ?case by simp
next case Num
  thus ?case by simp
next case Zero
  thus ?case by (metis eval_zero)
next case (Succ e)
  thus ?case 
  proof (cases "is_val e")
  case True  
    thus ?thesis by (cases e, simp_all, metis eval_suc_3)
  next case False
    with Succ eval_suc_1 show ?thesis by fastforce
  qed
next case (IsZ e1 e2 e3)
  thus ?case 
  proof (cases "is_val e1")
  case True  
    thus ?thesis
    proof (cases e1, simp_all)
      fix n
      show "Ex (eval (IsZ (Num n) e2 e3)) | error (IsZ (Num n) e2 e3)"
      by (cases n, metis eval_isz_3, metis eval_isz_4)
    qed
  next case False
    with IsZ eval_isz_1 show ?thesis by fastforce
  qed
next case Lam
  thus ?case by simp
next case (Appl e1 e2)
  thus ?case 
  proof (cases "is_val e1")
  case True  
    thus ?thesis by (cases e1, simp_all, metis eval_appl_4)
  next case False
    with Appl eval_appl_1 show ?thesis by fastforce
  qed
next case (Fix e)
  hence "eval (Fix e) (subst (Fix e) e)" by simp
  thus ?case by fast
qed

end
