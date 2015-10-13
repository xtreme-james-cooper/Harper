theory Chapter11_2_Typechecking
imports Chapter11_1_Language
begin

inductive typecheck :: "type env \<Rightarrow> expr \<Rightarrow> type \<Rightarrow> bool" where 
  tc_var [simp]: "lookup gam x = Some t \<Longrightarrow> typecheck gam (Var x) t"
| tc_zero [simp]: "typecheck gam Zero Nat"
| tc_suc [simp]: "typecheck gam e Nat \<Longrightarrow> typecheck gam (Suc e) Nat"
| tc_iter [simp]: "typecheck gam et Nat \<Longrightarrow> typecheck gam e0 t \<Longrightarrow> typecheck (extend gam t) es t \<Longrightarrow>
    typecheck gam (Iter et e0 es) t"
| tc_lam [simp]: "typecheck (extend gam t1) e t2 \<Longrightarrow> typecheck gam (Lam t1 e) (Arrow t1 t2)"
| tc_appl [simp]: "typecheck gam e1 (Arrow t2 t) \<Longrightarrow> typecheck gam e2 t2 \<Longrightarrow>
    typecheck gam (Appl e1 e2) t"
| tc_triv [simp]: "typecheck gam Triv Unit"
| tc_pair [simp]: "typecheck gam e1 t1 \<Longrightarrow> typecheck gam e2 t2 \<Longrightarrow>
    typecheck gam (Pair e1 e2) (Prod t1 t2)"
| tc_projl [simp]: "typecheck gam e (Prod t1 t2) \<Longrightarrow> typecheck gam (ProjL e) t1"
| tc_projr [simp]: "typecheck gam e (Prod t1 t2) \<Longrightarrow> typecheck gam (ProjR e) t2"
| tc_abort [simp]: "typecheck gam e Void \<Longrightarrow> typecheck gam (Abort t e) t"
| tc_case [simp]: "typecheck gam et (Sum t1 t2) \<Longrightarrow> typecheck (extend gam t1) el t \<Longrightarrow>
    typecheck (extend gam t2) er t \<Longrightarrow> typecheck gam (Case et el er) t"
| tc_inl [simp]: "typecheck gam e t1 \<Longrightarrow> typecheck gam (InL t1 t2 e) (Sum t1 t2)"
| tc_inr [simp]: "typecheck gam e t2 \<Longrightarrow> typecheck gam (InR t1 t2 e) (Sum t1 t2)"

inductive_cases [elim!]: "typecheck gam (Var x) t"
inductive_cases [elim!]: "typecheck gam Zero t"
inductive_cases [elim!]: "typecheck gam (Suc e) t"
inductive_cases [elim!]: "typecheck gam (Iter et e0 es) t"
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

lemma [simp]: "typecheck gam e t \<Longrightarrow> n in gam \<Longrightarrow> typecheck (extend_at n gam t') (insert n e) t"
  by (induction gam e t arbitrary: n rule: typecheck.induct) fastforce+

lemma [simp]: "typecheck (extend_at n gam t') e t \<Longrightarrow> n in gam \<Longrightarrow> typecheck gam e' t' \<Longrightarrow> 
    typecheck gam (subst e' n e) t"
  by (induction "extend_at n gam t'" e t arbitrary: n gam t' e' rule: typecheck.induct) fastforce+

end
