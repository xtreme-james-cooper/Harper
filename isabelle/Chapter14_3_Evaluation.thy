theory Chapter14_3_Evaluation
imports Chapter14_2_Typechecking
begin

primrec is_val :: "expr => bool"
where "is_val (Var v) = False"
    | "is_val Zero = True"
    | "is_val (Suc e) = is_val e"
    | "is_val (Rec et e0 es) = False"
    | "is_val (Lam t e) = True"
    | "is_val (Appl e1 e2) = False"
    | "is_val Triv = True"
    | "is_val (Pair e1 e2) = (is_val e1 & is_val e2)"
    | "is_val (ProjL e) = False"
    | "is_val (ProjR e) = False"
    | "is_val (Abort t e) = False"
    | "is_val (Case et el er) = False"
    | "is_val (InL t1 t2 e) = is_val e"
    | "is_val (InR t1 t2 e) = is_val e"

inductive eval :: "expr => expr => bool"
where eval_suc [simp]: "eval e e' ==> eval (Suc e) (Suc e')"
    | eval_rec_1 [simp]: "eval et et' ==> eval (Rec et e0 es) (Rec et e0 es)"
    | eval_rec_2 [simp]: "eval (Rec Zero e0 es) e0"
    | eval_rec_3 [simp]: "is_val et ==> 
            eval (Rec (Suc et) e0 es) (subst (Rec et e0 es) (subst et es))"
    | eval_appl_1 [simp]: "eval e1 e1' ==> eval (Appl e1 e2) (Appl e1' e2)"
    | eval_appl_2 [simp]: "is_val e1 ==> eval e2 e2' ==> eval (Appl e1 e2) (Appl e1 e2')"
    | eval_appl_3 [simp]: "is_val e2 ==> eval (Appl (Lam t2 e1) e2) (subst e2 e1)"
    | eval_pair_1 [simp]: "eval e1 e1' ==> eval (Pair e1 e2) (Pair e1' e2)"
    | eval_pair_2 [simp]: "is_val e1 ==> eval e2 e2' ==> eval (Pair e1 e2) (Pair e1 e2')"
    | eval_projl_1 [simp]: "eval e e' ==> eval (ProjL e) (ProjL e')"
    | eval_projl_2 [simp]: "eval (ProjL (Pair e1 e2)) e1"
    | eval_projr_1 [simp]: "eval e e' ==> eval (ProjR e) (ProjR e')"
    | eval_projr_2 [simp]: "eval (ProjR (Pair e1 e2)) e2"
    | eval_abort [simp]: "eval e e' ==> eval (Abort t e) (Abort t e')"
    | eval_case_1 [simp]: "eval et et' ==> eval (Case et el er) (Case et el er)"
    | eval_case_2 [simp]: "is_val e ==> eval (Case (InL t1 t2 e) el er) (subst e el)"
    | eval_case_3 [simp]: "is_val e ==> eval (Case (InR t1 t2 e) el er) (subst e er)"
    | eval_inl [simp]: "eval e e' ==> eval (InL t1 t2 e) (InL t1 t2 e')"
    | eval_inr [simp]: "eval e e' ==> eval (InR t1 t2 e) (InR t1 t2 e')"

lemma canonical_nat: "is_val e ==> typecheck gam e Nat ==> 
          e = Zero | (EX e'. e = Suc e' & typecheck gam e' Nat)"
by (induction e, auto)

lemma canonical_nat_no_vars: "is_val e ==> typecheck gam e Nat ==> typecheck gam' e Nat"
by (induction e, auto) 

lemma canonical_arrow: "is_val e ==> typecheck gam e (Arrow t1 t2) ==> 
              EX e'. e = Lam t1 e' & typecheck (extend gam t1) e' t2"
by (induction e, auto)

lemma canonical_triv: "is_val e ==> typecheck gam e Unit ==> e = Triv"
by (induction e, auto)

lemma canonical_pair: "is_val e ==> typecheck gam e (Prod t1 t2) ==> 
              EX e1 e2. e = Pair e1 e2 & typecheck gam e1 t1 & typecheck gam e2 t2"
by (induction e, auto)

lemma canonical_void: "is_val e ==> typecheck gam e Void ==> False"
by (induction e, auto)

lemma canonical_sum: "is_val e ==> typecheck gam e (Sum t1 t2) ==> 
          (EX e'. e = InL t1 t2 e' & typecheck gam e' t1) | 
          (EX e'. e = InR t1 t2 e' & typecheck gam e' t2)"
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
  from eval_rec_3 canonical_nat_no_vars have "typecheck (extend gam t) (subst et es) t" by auto
  with eval_rec_3 show ?case by fastforce
next case eval_appl_1 
  thus ?case by fastforce
next case eval_appl_2 
  thus ?case by fastforce
next case eval_appl_3 
  thus ?case by fastforce
next case eval_pair_1 
  thus ?case by fastforce
next case eval_pair_2 
  thus ?case by fastforce
next case eval_projl_1 
  thus ?case by fastforce
next case eval_projl_2 
  thus ?case by fastforce
next case eval_projr_1 
  thus ?case by fastforce
next case eval_projr_2 
  thus ?case by fastforce
next case eval_abort
  thus ?case by fastforce
next case eval_case_1 
  thus ?case by fastforce
next case eval_case_2 
  thus ?case by fastforce
next case eval_case_3 
  thus ?case by fastforce
next case eval_inl
  thus ?case by fastforce
next case eval_inr
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
next case tc_triv
  thus ?case by simp
next case tc_pair
  thus ?case by (metis eval_pair_1 eval_pair_2 is_val.simps(8))
next case tc_projl
  thus ?case by (metis eval_projl_1 eval_projl_2 canonical_pair)
next case tc_projr
  thus ?case by (metis eval_projr_1 eval_projr_2 canonical_pair)
next case tc_abort
  thus ?case by (metis eval_abort canonical_void)
next case tc_case
  thus ?case 
  by (metis eval_case_1 eval_case_2 eval_case_3 is_val.simps(13) is_val.simps(14) canonical_sum)
next case tc_inl
  thus ?case by (metis eval_inl is_val.simps(13))
next case tc_inr
  thus ?case by (metis eval_inr is_val.simps(14))
qed

end
