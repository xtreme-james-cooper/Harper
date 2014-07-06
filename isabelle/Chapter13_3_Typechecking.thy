theory Chapter13_3_Typechecking
imports Chapter13_2_Expressions
begin

inductive typecheck :: "type env => expr => type => bool"
where tc_var [simp]: "lookup gam x = Some t ==> typecheck gam (Var x) t"
    | tc_zero [simp]: "typecheck gam Zero Nat"
    | tc_suc [simp]: "typecheck gam e Nat ==> typecheck gam (Suc e) Nat"
    | tc_natrec [simp]: "typecheck gam et Nat ==> typecheck gam e0 t ==> 
                typecheck (extend (extend gam t) Nat) es t ==> typecheck gam (NatRec et e0 es) t"
    | tc_lam [simp]: "typecheck (extend gam t1) e t2 ==> typecheck gam (Lam t1 e) (Arrow t1 t2)"
    | tc_appl [simp]: "typecheck gam e1 (Arrow t2 t) ==> typecheck gam e2 t2 ==> 
                typecheck gam (Appl e1 e2) t"
    | tc_triv [simp]: "typecheck gam Triv Unit"
    | tc_pair [simp]: "typecheck gam e1 t1 ==> typecheck gam e2 t2 ==> 
                typecheck gam (Pair e1 e2) (Prod t1 t2)"
    | tc_projl [simp]: "typecheck gam e (Prod t1 t2) ==> typecheck gam (ProjL e) t1"
    | tc_projr [simp]: "typecheck gam e (Prod t1 t2) ==> typecheck gam (ProjR e) t2"
    | tc_abort [simp]: "typecheck gam e Void ==> typecheck gam (Abort t e) t"
    | tc_case [simp]: "typecheck gam et (Sum t1 t2) ==> typecheck (extend gam t1) el t ==> 
                typecheck (extend gam t2) er t ==> typecheck gam (Case et el er) t"
    | tc_inl [simp]: "typecheck gam e t1 ==> typecheck gam (InL t1 t2 e) (Sum t1 t2)"
    | tc_inr [simp]: "typecheck gam e t2 ==> typecheck gam (InR t1 t2 e) (Sum t1 t2)"
    | tc_map [simp]: "is_positive first t ==> typecheck (extend gam rho) e1 rho' ==> 
                typecheck gam e2 (type_subst rho t) ==> 
                        typecheck gam (Map t e1 e2) (type_subst rho' t)"

inductive_cases [elim!]: "typecheck gam (Var x) t"
inductive_cases [elim!]: "typecheck gam Zero t"
inductive_cases [elim!]: "typecheck gam (Suc e) t"
inductive_cases [elim!]: "typecheck gam (NatRec et e0 es) t"
inductive_cases [elim!]: "typecheck gam (Lam t1 e) t"
inductive_cases [elim!]: "typecheck gam (Appl e1 e2) t"
inductive_cases [elim!]: "typecheck gam Triv t"
inductive_cases [elim!]: "typecheck gam (Pair e1 e2) t"
inductive_cases [elim!]: "typecheck gam (ProjL e) t"
inductive_cases [elim!]: "typecheck gam (ProjR e) t"
inductive_cases [elim!]: "typecheck gam (Abort t1 e) t"
inductive_cases [elim!]: "typecheck gam (Case et el er) t"
inductive_cases [elim!]: "typecheck gam (InL t1 t2 e) t"
inductive_cases [elim!]: "typecheck gam (InR t1 t2 e) t"
inductive_cases [elim!]: "typecheck gam (Map t1 e1 e2) t"

lemma [simp]: "typecheck gam e t ==> n in gam ==> 
         typecheck (extend_at n gam t') (insert n e) t"
proof (induction gam e t arbitrary: n rule: typecheck.induct)
case tc_var
  thus ?case by fastforce
next case tc_zero
  thus ?case by fastforce
next case tc_suc
  thus ?case by fastforce
next case tc_natrec
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
next case (tc_map t gam rho e1 rho' e2)
  hence X: "extend_at first (extend_at n gam t') rho = 
                extend_at (next n) (extend_at first gam rho) t'" by simp
  from tc_map have "typecheck (extend_at (next n) (extend gam rho) t') (insert (next n) e1) rho'" by simp
  with X have "typecheck (extend (extend_at n gam t') rho) (insert (next n) e1) rho'" by simp
  with tc_map show ?case by fastforce
qed

lemma [simp]: "typecheck (extend_at n gam t') e t ==> n in gam ==> typecheck gam e' t' ==> 
        typecheck gam (remove n (subst' n (insert n e') e)) t"
proof (induction "extend_at n gam t'" e t arbitrary: n gam t' e' rule: typecheck.induct)
case tc_var
  thus ?case by fastforce
next case tc_zero
  thus ?case by fastforce
next case tc_suc
  thus ?case by fastforce
next case tc_natrec
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
next case (tc_map t rho e1 rho' e2)
  from tc_map have X: "is_positive first t" by simp
  from tc_map have Y: "typecheck (extend gam rho) (remove (next n) (subst' (next n) (insert first (insert n e')) e1)) rho'" by simp
  from tc_map have "typecheck gam (remove n (subst' n (insert n e') e2)) (type_subst rho t)" by simp
  with X Y show ?case by simp
qed

lemma [simp]: "typecheck (extend gam t') e t ==> typecheck gam e' t' ==> 
                          typecheck gam (subst e' e) t"
by (simp add: subst_def)

end
