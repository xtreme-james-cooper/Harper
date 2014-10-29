theory Chapter36_2_Typechecking
imports Chapter36_1_Language
begin

primrec is_mobile :: "type => bool"
where "is_mobile Nat = True"
    | "is_mobile (Arrow t1 t2) = False"
    | "is_mobile Unit = True"
    | "is_mobile (Prod t1 t2) = (is_mobile t1 & is_mobile t2)"
    | "is_mobile Void = True"
    | "is_mobile (Sum t1 t2) = (is_mobile t1 & is_mobile t2)"
    | "is_mobile (Command t) = False"

inductive typecheck :: "type env => type env => expr => type => bool"
      and typecheck_cmd :: "type env => type env => cmnd => type => bool"
where tc_var [simp]: "lookup gam x = Some t ==> typecheck gam sig (Var x) t"
    | tc_zero [simp]: "typecheck gam sig Zero Nat"
    | tc_suc [simp]: "typecheck gam sig e Nat ==> typecheck gam sig (Suc e) Nat"
    | tc_isz [simp]: "typecheck gam sig et Nat ==> typecheck gam sig e0 t ==> 
                typecheck (extend gam Nat) sig es t ==> typecheck gam sig (IsZ et e0 es) t"
    | tc_lam [simp]: "typecheck (extend gam t1) sig e t2 ==> 
                typecheck gam sig (Lam t1 e) (Arrow t1 t2)"
    | tc_appl [simp]: "typecheck gam sig e1 (Arrow t2 t) ==> typecheck gam sig e2 t2 ==> 
                typecheck gam sig (Appl e1 e2) t"
    | tc_triv [simp]: "typecheck gam sig Triv Unit"
    | tc_pair [simp]: "typecheck gam sig e1 t1 ==> typecheck gam sig e2 t2 ==> 
                typecheck gam sig (Pair e1 e2) (Prod t1 t2)"
    | tc_projl [simp]: "typecheck gam sig e (Prod t1 t2) ==> typecheck gam sig (ProjL e) t1"
    | tc_projr [simp]: "typecheck gam sig e (Prod t1 t2) ==> typecheck gam sig (ProjR e) t2"
    | tc_abort [simp]: "typecheck gam sig e Void ==> typecheck gam sig (Abort t e) t"
    | tc_case [simp]: "typecheck gam sig et (Sum t1 t2) ==> typecheck (extend gam t1) sig el t ==> 
                typecheck (extend gam t2) sig er t ==> typecheck gam sig (Case et el er) t"
    | tc_inl [simp]: "typecheck gam sig e t1 ==> typecheck gam sig (InL t1 t2 e) (Sum t1 t2)"
    | tc_inr [simp]: "typecheck gam sig e t2 ==> typecheck gam sig (InR t1 t2 e) (Sum t1 t2)"
    | tc_fix [simp]: "typecheck (extend gam t) sig e t ==> typecheck gam sig (Fix t e) t"
    | tc_cmd [simp]: "typecheck_cmd gam sig c t ==> typecheck gam sig (Cmd c) (Command t)"
    | tc_retn [simp]: "is_mobile t ==> typecheck gam sig e t ==> typecheck_cmd gam sig (Return e) t"
    | tc_bind [simp]: "typecheck gam sig e (Command t) ==> 
                typecheck_cmd (extend gam t) sig c t' ==> 
                      typecheck_cmd gam sig (Bind e c) t'"
    | tc_decl [simp]: "is_mobile t ==> typecheck gam sig e t ==> 
                typecheck_cmd gam (extend sig t) c t' ==>  typecheck_cmd gam sig (Declare e c) t'"
    | tc_get [simp]: "lookup sig v = Some t ==> typecheck_cmd gam sig (Get v) t"
    | tc_set [simp]: "lookup sig v = Some t ==> typecheck gam sig e t ==> 
                typecheck_cmd gam sig (Set v e) t"

inductive_cases [elim!]: "typecheck gam sig (Var x) t"
inductive_cases [elim!]: "typecheck gam sig Zero t"
inductive_cases [elim!]: "typecheck gam sig (Suc e) t"
inductive_cases [elim!]: "typecheck gam sig (IsZ et e0 es) t"
inductive_cases [elim!]: "typecheck gam sig (Lam t1 e) t"
inductive_cases [elim!]: "typecheck gam sig (Appl e1 e2) t"
inductive_cases [elim!]: "typecheck gam sig Triv t"
inductive_cases [elim!]: "typecheck gam sig (Pair e1 e2) t"
inductive_cases [elim!]: "typecheck gam sig (ProjL e) t"
inductive_cases [elim!]: "typecheck gam sig (ProjR e) t"
inductive_cases [elim!]: "typecheck gam sig (Abort t1 e) t"
inductive_cases [elim!]: "typecheck gam sig (Case et el er) t"
inductive_cases [elim!]: "typecheck gam sig (InL t1 t2 e) t"
inductive_cases [elim!]: "typecheck gam sig (InR t1 t2 e) t"
inductive_cases [elim!]: "typecheck gam sig (Fix t1 e) t"
inductive_cases [elim!]: "typecheck gam sig (Cmd c) t"
inductive_cases [elim!]: "typecheck_cmd gam sig (Return e) t"
inductive_cases [elim!]: "typecheck_cmd gam sig (Bind e c) t"
inductive_cases [elim!]: "typecheck_cmd gam sig (Declare e c) t"
inductive_cases [elim!]: "typecheck_cmd gam sig (Get v) t"
inductive_cases [elim!]: "typecheck_cmd gam sig (Set v e) t"

lemma [simp]: "typecheck gam sig e t ==> n in gam ==> 
         typecheck (extend_at n gam t') sig (insert n e) t"
  and [simp]: "typecheck_cmd gam sig c t ==> n in gam ==> 
         typecheck_cmd (extend_at n gam t') sig (insert_cmd n c) t"
by (induction arbitrary: n and n rule: typecheck_typecheck_cmd.inducts, fastforce+)

lemma [simp]: "typecheck (extend_at n gam t') sig e t ==> n in gam ==> typecheck gam sig e' t' ==> 
        typecheck gam sig (remove n (subst' n (insert n e') e)) t"
  and [simp]: "typecheck_cmd (extend_at n gam t') sig c t ==> n in gam ==> 
        typecheck gam sig e' t' ==> 
                typecheck_cmd gam sig (remove_cmd n (subst_cmd' n (insert n e') c)) t"
proof (induction "extend_at n gam t'" sig e t and "extend_at n gam t'" sig c t
       arbitrary: n gam t' e' and n gam t' e' rule: typecheck_typecheck_cmd.inducts)
case tc_var
  thus ?case by fastforce
next case tc_zero
  thus ?case by fastforce
next case tc_suc
  thus ?case by fastforce
next case tc_isz
  thus ?case by fastforce
next case tc_lam
  thus ?case by fastforce
next case tc_appl
  thus ?case by fastforce
next case tc_triv
  thus ?case by fastforce
next case tc_pair
  thus ?case by fastforce
next case tc_projl
  thus ?case by fastforce
next case tc_projr
  thus ?case by fastforce
next case tc_abort
  thus ?case by fastforce
next case tc_case
  thus ?case by fastforce
next case tc_inl
  thus ?case by fastforce
next case tc_inr
  thus ?case by fastforce
next case tc_fix
  thus ?case by fastforce
next case tc_cmd
  thus ?case by fastforce
next case tc_retn
  thus ?case by fastforce
next case tc_bind
  thus ?case by fastforce
next case (tc_decl t sig e)

  hence "typecheck gam (extend sig t) e' t'" by simp sorry
  with tc_decl show ?case by simp
next case tc_get
  thus ?case by fastforce
next case tc_set
  thus ?case by fastforce
qed 

lemma [simp]: "typecheck (extend gam t') sig e t ==> typecheck gam sig e' t' ==> 
                          typecheck gam sig (subst e' e) t"
by (simp add: subst_def)

lemma [simp]: "typecheck_cmd (extend gam t') sig c t ==> typecheck gam sig e' t' ==> 
                          typecheck_cmd gam sig (subst_cmd e' c) t"
by (simp add: subst_cmd_def)

end
