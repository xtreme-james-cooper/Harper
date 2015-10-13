theory Chapter09_2_Typechecking
imports Chapter09_1_Language
begin

inductive typecheck :: "type env \<Rightarrow> expr \<Rightarrow> type \<Rightarrow> bool" where 
  tc_var [simp]: "lookup gam x = Some t \<Longrightarrow> typecheck gam (Var x) t"
| tc_zero [simp]: "typecheck gam Zero Nat"
| tc_suc [simp]: "typecheck gam e Nat \<Longrightarrow> typecheck gam (Suc e) Nat"
| tc_rec [simp]: "typecheck gam et Nat \<Longrightarrow> typecheck gam e0 t \<Longrightarrow> 
    typecheck (extend (extend gam t) Nat) es t \<Longrightarrow> typecheck gam (Rec et e0 es) t"
| tc_lam [simp]: "typecheck (extend gam t1) e t2 \<Longrightarrow> typecheck gam (Lam t1 e) (Arrow t1 t2)"
| tc_appl [simp]: "typecheck gam e1 (Arrow t2 t) \<Longrightarrow> typecheck gam e2 t2 \<Longrightarrow> 
    typecheck gam (Appl e1 e2) t"

inductive_cases [elim!]: "typecheck gam (Var x) t"
inductive_cases [elim!]: "typecheck gam Zero t"
inductive_cases [elim!]: "typecheck gam (Suc e) t"
inductive_cases [elim!]: "typecheck gam (Rec et e0 es) t"
inductive_cases [elim!]: "typecheck gam (Lam t1 e) t"
inductive_cases [elim!]: "typecheck gam (Appl e1 e2) t"

lemma [simp]: "typecheck gam e t \<Longrightarrow> n in gam \<Longrightarrow> typecheck (extend_at n gam t') (insert n e) t"
  by (induction gam e t arbitrary: n rule: typecheck.induct) fastforce+

lemma [simp]: "typecheck (extend_at n gam t') e t \<Longrightarrow> n in gam \<Longrightarrow> typecheck gam e' t' \<Longrightarrow>
    typecheck gam (subst e' n e) t"
  by (induction "extend_at n gam t'" e t arbitrary: n gam t' e' rule: typecheck.induct) fastforce+

end
