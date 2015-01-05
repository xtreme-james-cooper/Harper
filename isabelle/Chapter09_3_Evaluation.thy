theory Chapter09_3_Evaluation
imports Chapter09_2_Typechecking
begin

primrec is_val :: "expr => bool"
where "is_val (Var v) = False"
    | "is_val Zero = True"
    | "is_val (Suc e) = is_val e"
    | "is_val (Rec et e0 es) = False"
    | "is_val (Lam t e) = True"
    | "is_val (Appl e1 e2) = False"

inductive eval :: "expr => expr => bool"
where eval_suc [simp]: "eval e e' ==> eval (Suc e) (Suc e')"
    | eval_rec_1 [simp]: "eval et et' ==> eval (Rec et e0 es) (Rec et' e0 es)"
    | eval_rec_2 [simp]: "eval (Rec Zero e0 es) e0"
    | eval_rec_3 [simp]: "is_val et ==> 
            eval (Rec (Suc et) e0 es) (subst (Rec et e0 es) first (subst et first es))"
    | eval_appl_1 [simp]: "eval e1 e1' ==> eval (Appl e1 e2) (Appl e1' e2)"
    | eval_appl_2 [simp]: "is_val e1 ==> eval e2 e2' ==> eval (Appl e1 e2) (Appl e1 e2')"
    | eval_appl_3 [simp]: "is_val e2 ==> eval (Appl (Lam t2 e1) e2) (subst e2 first e1)"

lemma canonical_nat: "is_val e ==> typecheck gam e Nat ==> 
          e = Zero | (EX e'. e = Suc e' & typecheck gam e' Nat)"
by (induction e, auto)

lemma canonical_nat_no_vars: "is_val e ==> typecheck gam e Nat ==> typecheck gam' e Nat"
by (induction e, auto) 

lemma canonical_arrow: "is_val e ==> typecheck gam e (Arrow t1 t2) ==> 
              EX e'. e = Lam t1 e' & typecheck (extend gam t1) e' t2"
by (induction e, auto)

theorem preservation: "eval e e' ==> typecheck gam e t ==> typecheck gam e' t"
proof (induction e e' arbitrary: t rule: eval.induct)
case eval_suc 
  thus ?case by fastforce
next case eval_rec_1 
  thus ?case by fastforce
next case eval_rec_2 
  thus ?case by fastforce
next case (eval_rec_3 et e0 es)
  from eval_rec_3 canonical_nat_no_vars have "typecheck (extend gam t) (subst et first es) t" by auto
  with eval_rec_3 show ?case by fastforce
next case eval_appl_1 
  thus ?case by fastforce
next case eval_appl_2 
  thus ?case by fastforce
next case eval_appl_3 
  thus ?case by fastforce
qed

theorem progress: "typecheck gam e t ==> gam = empty_env ==> is_val e | (EX e'. eval e e')"
proof (induction gam e t rule: typecheck.induct)
case tc_var
  thus ?case by simp
next case tc_zero
  thus ?case by simp
next case tc_suc
  thus ?case by (metis eval_suc is_val.simps(3))
next case tc_rec
  thus ?case by (metis eval_rec_1 eval_rec_2 eval_rec_3 is_val.simps(3) canonical_nat)
next case tc_lam
  thus ?case by simp
next case tc_appl
  thus ?case by (metis eval_appl_1 eval_appl_2 eval_appl_3 canonical_arrow)
qed

end
