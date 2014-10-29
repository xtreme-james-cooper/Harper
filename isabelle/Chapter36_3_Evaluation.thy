theory Chapter36_3_Evaluation
imports Chapter36_2_Typechecking
begin

primrec is_val :: "expr => bool"
    and is_val_cmd :: "cmnd => bool"
where "is_val (Var v) = False"
    | "is_val Zero = True"
    | "is_val (Suc e) = is_val e"
    | "is_val (IsZ et e0 es) = False"
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
    | "is_val (Fix t e) = False"
    | "is_val (Cmd c) = True"
    | "is_val_cmd (Return e) = is_val e"
    | "is_val_cmd (Bind e c) = False"
    | "is_val_cmd (Declare e c) = False"
    | "is_val_cmd (Get v) = False"
    | "is_val_cmd (Set v e) = False"

lemma mobile_indep_sig: "typecheck gam sig e t ==> gam = empty_env ==> is_mobile t ==> is_val e ==> 
      typecheck gam' sig' e t"
  and mobile_indep_sig_cmd: "typecheck_cmd gam sig c t ==> gam = empty_env ==> is_mobile t ==> is_val_cmd c ==> 
      typecheck_cmd gam' sig' c t"
by (induction rule: typecheck_typecheck_cmd.inducts, simp_all)

definition conforms_to :: "expr env => type env => bool"
where "conforms_to = conform_envs (%e t. is_val e & is_mobile t & typecheck empty_env empty_env e t)"

inductive eval :: "expr => expr => bool"
      and eval_cmd :: "cmnd => expr env => cmnd => expr env => bool"
where eval_suc [simp]: "eval e e' ==> eval (Suc e) (Suc e')"
    | eval_isz_1 [simp]: "eval et et' ==> eval (IsZ et e0 es) (IsZ et' e0 es)"
    | eval_isz_2 [simp]: "eval (IsZ Zero e0 es) e0"
    | eval_isz_3 [simp]: "is_val et ==> eval (IsZ (Suc et) e0 es) (subst et es)"
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
    | eval_case_1 [simp]: "eval et et' ==> eval (Case et el er) (Case et' el er)"
    | eval_case_2 [simp]: "is_val e ==> eval (Case (InL t1 t2 e) el er) (subst e el)"
    | eval_case_3 [simp]: "is_val e ==> eval (Case (InR t1 t2 e) el er) (subst e er)"
    | eval_inl [simp]: "eval e e' ==> eval (InL t1 t2 e) (InL t1 t2 e')"
    | eval_inr [simp]: "eval e e' ==> eval (InR t1 t2 e) (InR t1 t2 e')"
    | eval_fix [simp]: "eval (Fix t e) (subst (Fix t e) e)"
    | eval_ret [simp]: "eval e e' ==> eval_cmd (Return e) s (Return e') s"
    | eval_bind_1 [simp]: "eval e e' ==> eval_cmd (Bind e c) s (Bind e' c) s"
    | eval_bind_2 [simp]: "eval_cmd c s c' s' ==> eval_cmd (Bind (Cmd c) c2) s (Bind (Cmd c') c2) s'"
    | eval_bind_3 [simp]: "is_val e ==> eval_cmd (Bind (Cmd (Return e)) c) s (subst_cmd e c) s"
    | eval_decl_1 [simp]: "eval e e' ==> eval_cmd (Declare e c) s (Declare e' c) s"
    | eval_decl_2 [simp]: "is_val e ==> eval_cmd c (extend s e) c' s' ==>
                eval_cmd (Declare e c) s (Declare e c') s'"
    | eval_decl_3 [simp]: "is_val e ==> is_val e2 ==> 
                eval_cmd (Delcare e (Return e2)) s (Return e2) s'"
    | eval_get [simp]: "lookup s v = Some e ==> eval_cmd (Get v) s (Return e) s"
    | eval_set_1 [simp]: "eval e e' ==> eval_cmd (Set v e) s (Set v e') s"
    | eval_set_2 [simp]: "is_val e ==> eval_cmd (Set v e) s (Return e) (update s v e)"

lemma canonical_nat: "is_val e ==> typecheck gam sig e Nat ==> 
          e = Zero | (EX e'. e = Suc e' & typecheck gam sig e' Nat)"
by (induction e, auto)

lemma canonical_nat_no_vars: "is_val e ==> typecheck gam sig e Nat ==> typecheck gam' sig e Nat"
by (induction e, auto)

lemma canonical_arrow: "is_val e ==> typecheck gam sig e (Arrow t1 t2) ==> 
              EX e'. e = Lam t1 e' & typecheck (extend gam t1) sig e' t2"
by (induction e, auto)

lemma canonical_unit: "is_val e ==> typecheck gam sig e Unit ==> e = Triv"
by (induction e, auto)

lemma canonical_prod: "is_val e ==> typecheck gam sig e (Prod t1 t2) ==> 
              EX e1 e2. e = Pair e1 e2 & typecheck gam sig e1 t1 & typecheck gam sig e2 t2"
by (induction e, auto)

lemma canonical_void: "is_val e ==> typecheck gam sig e Void ==> False"
by (induction e, auto)

lemma canonical_sum: "is_val e ==> typecheck gam sig e (Sum t1 t2) ==> 
          (EX e'. e = InL t1 t2 e' & typecheck gam sig e' t1) | 
          (EX e'. e = InR t1 t2 e' & typecheck gam sig e' t2)"
by (induction e, auto)

lemma canonical_command: "is_val e ==> typecheck gam sig e (Command t) ==> 
          EX c. e = Cmd c & typecheck_cmd gam sig c t"
by (induction e, auto)

theorem preservation: "eval e e' ==> typecheck gam sig e t ==> typecheck gam sig e' t"
    and preservation_cmd: "eval_cmd c s c' s' ==> conforms_to s sig ==> typecheck_cmd gam sig c t ==> 
              typecheck_cmd gam sig c' t & conforms_to s' sig"
proof (induction arbitrary: t and t rule: eval_eval_cmd.inducts)
case eval_suc
  thus ?case by fastforce
next case eval_isz_1
  thus ?case by fastforce
next case eval_isz_2
  thus ?case by fastforce
next case eval_isz_3
  thus ?case by fastforce
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
next case eval_fix
  thus ?case by fastforce
next case eval_ret
  thus ?case by fastforce
next case eval_bind_1
  thus ?case by fastforce
next case (eval_bind_2 c s c' s' c2)
  then obtain tt where "typecheck_cmd gam sig c tt & typecheck_cmd (extend gam tt) sig c2 t" 
  by force
  with eval_bind_2 show ?case by (metis tc_bind tc_cmd)
next case eval_bind_3
  thus ?case by fastforce
next case eval_decl_1
  thus ?case by fastforce
next case (eval_decl_2 e c s c' s')
  then obtain tt where "is_mobile tt & typecheck gam sig e tt & 
          typecheck_cmd gam (extend sig tt) c t" by fast

  have "typecheck_cmd gam sig (Declare e c') t & conforms_to s' sig" by simp sorry
  thus ?case by simp
next case eval_decl_3
  thus ?case by simp sorry
next case (eval_get s v e)
  from eval_get have X: "lookup s v = Some e" by simp
  from eval_get have Y: "lookup sig v = Some t" by fast
  from eval_get have "conform_envs (%e t. is_val e & is_mobile t & typecheck empty_env empty_env e t) s sig" by (simp add: conforms_to_def) 

  with X Y have "is_val e & is_mobile t & typecheck empty_env empty_env e t" by simp sorry
  with mobile_indep_sig have "is_mobile t & typecheck gam sig e t" by fast
  with eval_get show ?case by simp
next case eval_set_1
  thus ?case by fastforce
next case eval_set_2
  thus ?case by simp sorry
qed

theorem progress: "typecheck gam sig e t ==> gam = empty_env ==> is_val e | (EX e'. eval e e')"
    and progress_cmd: "typecheck_cmd gam sig c t ==> gam = empty_env ==> conforms_to s sig ==>
              is_val_cmd c | (EX c' s'. eval_cmd c s c' s')"
proof (induction rule: typecheck_typecheck_cmd.inducts)
case tc_var
  thus ?case by simp
next case tc_zero
  thus ?case by simp
next case tc_suc
  thus ?case by (metis eval_suc is_val_is_val_cmd.simps(3))
next case tc_isz
  thus ?case by (metis eval_isz_1 eval_isz_2 eval_isz_3 is_val_is_val_cmd.simps(3) canonical_nat)
next case tc_lam
  thus ?case by simp
next case tc_appl
  thus ?case by (metis eval_appl_1 eval_appl_2 eval_appl_3 canonical_arrow)
next case tc_triv
  thus ?case by simp
next case tc_pair
  thus ?case by (metis eval_pair_1 eval_pair_2 is_val_is_val_cmd.simps(8))
next case tc_projl
  thus ?case by (metis eval_projl_1 eval_projl_2 canonical_prod)
next case tc_projr
  thus ?case by (metis eval_projr_1 eval_projr_2 canonical_prod)
next case tc_abort
  thus ?case by (metis eval_abort canonical_void)
next case tc_case
  thus ?case 
  by (metis eval_case_1 eval_case_2 eval_case_3 is_val_is_val_cmd.simps(13) 
            is_val_is_val_cmd.simps(14) canonical_sum)
next case tc_inl
  thus ?case by (metis eval_inl is_val_is_val_cmd.simps(13))
next case tc_inr
  thus ?case by (metis eval_inr is_val_is_val_cmd.simps(14))
next case tc_fix
  thus ?case by (metis eval_fix)
next case tc_cmd
  thus ?case by simp
next case tc_retn
  thus ?case by (metis eval_ret is_val_is_val_cmd.simps(17))
next case (tc_bind gam sig e c)
  thus ?case by simp sorry
next case tc_decl
  thus ?case by simp sorry
next case (tc_get v sig gam)
  thus ?case by simp sorry
next case tc_set
  thus ?case by simp sorry
qed

end
