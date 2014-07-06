theory Chapter20_2_Typechecking
imports Chapter20_1_Language
begin

primrec is_type :: "var => type => bool"
where "is_type del (Tyvar v) = canswap v del"
    | "is_type del Nat = True"
    | "is_type del (Arrow e1 e2) = (is_type del e1 & is_type del e2)"
    | "is_type del (All e) = is_type (next del) e"
    | "is_type del Unit = True"
    | "is_type del (Prod e1 e2) = (is_type del e1 & is_type del e2)"
    | "is_type del Void = True"
    | "is_type del (Sum e1 e2) = (is_type del e1 & is_type del e2)"

inductive typecheck :: "var => type env => expr => type => bool"
where tc_var [simp]: "lookup gam x = Some t ==> typecheck del gam (Var x) t"
    | tc_zero [simp]: "typecheck del gam Zero Nat"
    | tc_suc [simp]: "typecheck del gam e Nat ==> typecheck del gam (Suc e) Nat"
    | tc_rec [simp]: "typecheck del gam et Nat ==> typecheck del gam e0 t ==> 
                typecheck del (extend gam t) es t ==> typecheck del gam (Iter et e0 es) t"
    | tc_lam [simp]: "is_type del t1 ==> typecheck del (extend gam t1) e t2 ==> 
                typecheck del gam (Lam t1 e) (Arrow t1 t2)"
    | tc_appl [simp]: "typecheck del gam e1 (Arrow t2 t) ==> typecheck del gam e2 t2 ==> 
                typecheck del gam (Appl e1 e2) t"
    | tc_tylam [simp]: "typecheck (next del) gam e t ==> typecheck del gam (TyLam e) (All t)"
    | tc_tyappl [simp]: "is_type del t' ==> typecheck del gam e (All t) ==> 
                typecheck del gam (TyAppl t' e) (type_subst first t' t)"
    | tc_triv [simp]: "typecheck del gam Triv Unit"
    | tc_pair [simp]: "typecheck del gam e1 t1 ==> typecheck del gam e2 t2 ==> 
                typecheck del gam (Pair e1 e2) (Prod t1 t2)"
    | tc_projl [simp]: "typecheck del gam e (Prod t1 t2) ==> typecheck del gam (ProjL e) t1"
    | tc_projr [simp]: "typecheck del gam e (Prod t1 t2) ==> typecheck del gam (ProjR e) t2"
    | tc_abort [simp]: "is_type del t ==> typecheck del gam e Void ==> 
                typecheck del gam (Abort t e) t"
    | tc_case [simp]: "typecheck del gam et (Sum t1 t2) ==> typecheck del (extend gam t1) el t ==> 
                typecheck del (extend gam t2) er t ==> typecheck del gam (Case et el er) t"
    | tc_inl [simp]: "is_type del t1 ==> is_type del t2 ==> typecheck del gam e t1 ==> 
                typecheck del gam (InL t1 t2 e) (Sum t1 t2)"
    | tc_inr [simp]: "is_type del t1 ==> is_type del t2 ==> typecheck del gam e t2 ==> 
                typecheck del gam (InR t1 t2 e) (Sum t1 t2)"

inductive_cases [elim!]: "typecheck del gam (Var x) t"
inductive_cases [elim!]: "typecheck del gam Zero t"
inductive_cases [elim!]: "typecheck del gam (Suc e) t"
inductive_cases [elim!]: "typecheck del gam (Iter et e0 es) t"
inductive_cases [elim!]: "typecheck del gam (Lam t1 e) t"
inductive_cases [elim!]: "typecheck del gam (Appl e1 e2) t"
inductive_cases [elim!]: "typecheck del gam (TyLam e) t"
inductive_cases [elim!]: "typecheck del gam (TyAppl e1 e2) t"
inductive_cases [elim!]: "typecheck del gam Triv t"
inductive_cases [elim!]: "typecheck del gam (Pair e1 e2) t"
inductive_cases [elim!]: "typecheck del gam (ProjL e) t"
inductive_cases [elim!]: "typecheck del gam (ProjR e) t"
inductive_cases [elim!]: "typecheck del gam (Abort t1 e) t"
inductive_cases [elim!]: "typecheck del gam (Case et el er) t"
inductive_cases [elim!]: "typecheck del gam (InL t1 t2 e) t"
inductive_cases [elim!]: "typecheck del gam (InR t1 t2 e) t"

lemma [simp]: "typecheck del gam e t ==> n in gam ==> 
         typecheck del (extend_at n gam t') (insert n e) t"
by (induction del gam e t arbitrary: n rule: typecheck.induct, fastforce+)

lemma [simp]: "is_type del t ==> is_type (next del) t"
by (induction t arbitrary: del, simp_all)

lemma [simp]: "typecheck del gam e t ==> typecheck (next del) gam e t"
by (induction del gam e t rule: typecheck.induct, simp_all)

lemma [simp]: "typecheck del (extend_at n gam t') e t ==> n in gam ==> typecheck del gam e' t' ==> 
        typecheck del gam (remove n (subst' n (insert n e') e)) t"
by (induction del "extend_at n gam t'" e t arbitrary: n gam t' e' rule: typecheck.induct, fastforce+)

lemma [simp]: "typecheck del (extend gam t') e t ==> typecheck del gam e' t' ==> 
                          typecheck del gam (subst e' e) t"
by (simp add: subst_def)

lemma [simp]: "is_type del t ==> is_type (next del) (type_insert n t)"
by (induction t arbitrary: n del, simp_all)

lemma [simp]: "is_type (next del) t ==> is_type del t' ==> 
                is_type del (type_remove n (type_subst' n (type_insert n t') t))"
proof (induction t arbitrary: n del t')
case (Tyvar v) 
  thus ?case by simp sorry
next case Nat 
  thus ?case by simp
next case (Arrow e1 e2)
  thus ?case by simp
next case (All e) 
  thus ?case by simp
next case Unit 
  thus ?case by simp
next case (Prod e1 e2) 
  thus ?case by simp
next case Void 
  thus ?case by simp
next case (Sum e1 e2) 
  thus ?case by simp
qed 

lemma [simp]: "is_type (next del) t ==> is_type del t' ==> is_type del (type_subst first t' t)"
by (simp add: type_subst_def)

lemma [simp]: "typecheck (next del) gam e t ==> 
        typecheck del (env_map (%t. type_remove n (type_subst' n (type_insert n t') t)) gam) 
                  (subst_type n t' e) 
                  (type_remove n (type_subst' n (type_insert n t') t))"
proof (induction "next del" gam e t arbitrary: del t' n rule: typecheck.induct)
case tc_var
  thus ?case by simp
next case tc_zero
  thus ?case by simp
next case tc_suc
  thus ?case by simp
next case (tc_rec gam et e0 t es)
  thus ?case by simp sorry
next case (tc_lam gam t1 e t2)
  thus ?case by simp sorry
next case (tc_appl gam e1 t2 t e2)
  thus ?case by simp sorry
next case (tc_tylam gam e t)
  thus ?case by simp sorry
next case (tc_tyappl gam e t t2)
  thus ?case by simp sorry
next case tc_triv
  thus ?case by simp
next case tc_pair
  thus ?case by simp
next case tc_projl
  thus ?case 
  by (metis subst_type.simps(11) type_remove.simps(6) type_subst'.simps(6) typecheck.tc_projl)
next case tc_projr
  thus ?case 
  by (metis subst_type.simps(12) type_remove.simps(6) type_subst'.simps(6) typecheck.tc_projr)
next case (tc_abort t gam e)
  from tc_abort have "is_type (next del) t" by simp
  from tc_abort have "typecheck (next del) gam e Void" by simp

  have X: "is_type del (type_subst n t' t)" by simp sorry
  with tc_abort show ?case by (simp add: type_subst_def)
next case tc_case
  thus ?case by simp sorry
next case tc_inl
  thus ?case by simp sorry
next case tc_inr
  thus ?case by simp sorry
qed

lemma [simp]: "typecheck (next del) gam e t ==> 
        typecheck del (env_map (%v. type_subst n t' v) gam) (subst_type n t' e) (type_subst n t' t)"
by (simp add: type_subst_def)

lemma [simp]: "typecheck (next del) gam e t ==> 
        typecheck del (env_map (type_subst n t') gam) (subst_type n t' e) (type_subst n t' t)"
by auto

end
