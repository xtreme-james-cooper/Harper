theory Chapter08_2_Typechecking
imports Chapter08_1_Language
begin

inductive typecheck :: "type env \<Rightarrow> expr \<Rightarrow> type \<Rightarrow> bool" where 
  tc_var [simp]: "gam x = Some t \<Longrightarrow> typecheck gam (Var x) t"
| tc_str [simp]: "typecheck gam (Str s) StrType"
| tc_num [simp]: "typecheck gam (Num n) NumType"
| tc_plus [simp]: "typecheck gam e1 NumType \<Longrightarrow> typecheck gam e2 NumType \<Longrightarrow>
    typecheck gam (Plus e1 e2) NumType"
| tc_times [simp]: "typecheck gam e1 NumType \<Longrightarrow> typecheck gam e2 NumType \<Longrightarrow> 
    typecheck gam (Times e1 e2) NumType"
| tc_cat [simp]: "typecheck gam e1 StrType \<Longrightarrow> typecheck gam e2 StrType \<Longrightarrow>
    typecheck gam (Cat e1 e2) StrType"
| tc_len [simp]: "typecheck gam e StrType \<Longrightarrow> typecheck gam (Len e) NumType"
| tc_let [simp]: "typecheck gam e1 t1 \<Longrightarrow> 
    (\<And>n e2'. n \<notin> dom gam \<Longrightarrow> e2 n = Some e2' \<Longrightarrow> typecheck (gam (n \<mapsto> t1)) e2' t2) \<Longrightarrow> 
      typecheck gam (Let e1 e2) t2"
| tc_lam [simp]: "(\<And>n e'. n \<notin> dom gam \<Longrightarrow> e n = Some e' \<Longrightarrow> typecheck (gam (n \<mapsto> t1)) e' t2) \<Longrightarrow> 
    typecheck gam (Lam t1 e) (Arrow t1 t2)"
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

lemma [elim]: "typecheck gam e t \<Longrightarrow> n \<notin> dom gam \<Longrightarrow> typecheck (gam(n \<mapsto> t')) e t"
  proof (induction gam e t rule: typecheck.induct)
  case (tc_var gam x t)
    hence "(gam(n \<mapsto> t')) x = Some t" by auto
    thus ?case by auto
  next case tc_str
    thus ?case by simp
  next case tc_num
    thus ?case by simp
  next case tc_plus
    thus ?case by simp
  next case tc_times
    thus ?case by simp
  next case tc_cat
    thus ?case by simp
  next case tc_len
    thus ?case by simp
  next case (tc_let gam e1 t1 e2 t2)
    hence "typecheck (gam(n \<mapsto> t')) e1 t1" by fastforce
    moreover have "\<And>m e2'. m \<notin> dom (gam(n \<mapsto> t')) \<Longrightarrow> e2 n = Some e2' \<Longrightarrow> typecheck ((gam(n \<mapsto> t')) (m \<mapsto> t1)) e2' t2"
      proof -
        fix m e2'
        assume "m \<notin> dom (gam(n \<mapsto> t'))"
           and "e2 n = Some e2'"
        

        show "typecheck (gam(n \<mapsto> t', m \<mapsto> t1)) e2' t2" by simp
      qed
    ultimately show ?case try
  next case tc_lam
    thus ?case by simp
  next case tc_appl
    thus ?case by simp
  qed 

lemma [simp]: "typecheck (gam(n \<mapsto> t')) e t \<Longrightarrow> typecheck gam e' t' \<Longrightarrow>
    typecheck gam (subst e' n e) t"
  proof (induction "gam(n \<mapsto> t')" e t arbitrary: n gam t' e' rule: typecheck.induct)
  case tc_var
    thus ?case by auto
  next case tc_str
    thus ?case by simp
  next case tc_num
    thus ?case by simp
  next case tc_plus
    thus ?case by simp
  next case tc_times
    thus ?case by simp
  next case tc_cat
    thus ?case by simp
  next case tc_len
    thus ?case by simp
  next case (tc_let e1 t1 e2 t2)
    hence "typecheck gam (subst e' n e1) t1" by simp
    moreover have "\<And>m. m \<notin> dom gam \<Longrightarrow> typecheck (gam (m \<mapsto> t1)) (subst e' n (e2 m)) t2"
      proof -
        fix m
        assume "m \<notin> dom gam"
        from tc_let have "typecheck gam e' t'" by simp


        have X: "m \<notin> dom (gam(n \<mapsto> t'))" by simp


        have Y: "gam(n \<mapsto> t', m \<mapsto> t1) = gam (m \<mapsto> t1, n \<mapsto> t')" by simp


        have "typecheck (gam (m \<mapsto> t1)) e' t'" by simp
        with X Y tc_let show "typecheck (gam (m \<mapsto> t1)) (subst e' n (e2 m)) t2" by simp
      qed
    ultimately show ?case by simp
  next case tc_lam
    thus ?case by simp
  next case tc_appl
    thus ?case by simp
  qed 

end
