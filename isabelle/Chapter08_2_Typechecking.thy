theory Chapter08_2_Typechecking
imports Chapter08_1_Language
begin

inductive typecheck :: "type env \<Rightarrow> expr \<Rightarrow> type \<Rightarrow> bool" where 
  tc_var [simp]: "lookup gam x = Some t \<Longrightarrow> typecheck gam (Var x) t"
| tc_str [simp]: "typecheck gam (Str s) StrType"
| tc_num [simp]: "typecheck gam (Num n) NumType"
| tc_plus [simp]: "typecheck gam e1 NumType \<Longrightarrow> typecheck gam e2 NumType \<Longrightarrow>
    typecheck gam (Plus e1 e2) NumType"
| tc_times [simp]: "typecheck gam e1 NumType \<Longrightarrow> typecheck gam e2 NumType \<Longrightarrow> 
    typecheck gam (Times e1 e2) NumType"
| tc_cat [simp]: "typecheck gam e1 StrType \<Longrightarrow> typecheck gam e2 StrType \<Longrightarrow>
    typecheck gam (Cat e1 e2) StrType"
| tc_len [simp]: "typecheck gam e StrType \<Longrightarrow> typecheck gam (Len e) NumType"
| tc_let [simp]: "typecheck gam e1 t1 \<Longrightarrow> typecheck (extend gam t1) e2 t2 \<Longrightarrow>
    typecheck gam (Let e1 e2) t2"
| tc_lam [simp]: "typecheck (extend gam t1) e t2 \<Longrightarrow> typecheck gam (Lam t1 e) (Arrow t1 t2)"
| tc_appl [simp]: "typecheck gam e1 (Arrow t2 t) \<Longrightarrow> typecheck gam e2 t2 \<Longrightarrow>
    typecheck gam (Appl e1 e2) t"

inductive_cases [elim!]: "typecheck gam (Var x) t"
inductive_cases [elim!]: "typecheck gam (Str s) t"
inductive_cases [elim!]: "typecheck gam (Num n) t"
inductive_cases [elim!]: "typecheck gam (Plus e1 e2) t"
inductive_cases [elim!]: "typecheck gam (Times e1 e2) t"
inductive_cases [elim!]: "typecheck gam (Cat e1 e2) t"
inductive_cases [elim!]: "typecheck gam (Len e) t"
inductive_cases [elim!]: "typecheck gam (Let e1 e2) t"
inductive_cases [elim!]: "typecheck gam (Lam t1 e) t"
inductive_cases [elim!]: "typecheck gam (Appl e1 e2) t"

lemma [simp]: "typecheck gam e t \<Longrightarrow> n in gam \<Longrightarrow> typecheck (extend_at n gam t') (insert n e) t"
  by (induction gam e t arbitrary: n rule: typecheck.induct) fastforce+

lemma [simp]: "typecheck (extend_at n gam t') e t \<Longrightarrow> n in gam \<Longrightarrow> typecheck gam e' t' \<Longrightarrow>
    typecheck gam (subst e' n e) t"
  by (induction "extend_at n gam t'" e t arbitrary: n gam t' e' rule: typecheck.induct) fastforce+

end
