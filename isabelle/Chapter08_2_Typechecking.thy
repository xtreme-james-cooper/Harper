theory Chapter08_2_Typechecking
imports Chapter08_1_Language
begin

inductive typecheck :: "type env => expr => type => bool"
where tc_var [simp]: "lookup gam x = Some t ==> typecheck gam (Var x) t"
    | tc_str [simp]: "typecheck gam (Str s) StrType"
    | tc_num [simp]: "typecheck gam (Num n) NumType"
    | tc_plus [simp]: "typecheck gam e1 NumType ==> typecheck gam e2 NumType ==> 
                    typecheck gam (Plus e1 e2) NumType"
    | tc_times [simp]: "typecheck gam e1 NumType ==> typecheck gam e2 NumType ==> 
                    typecheck gam (Times e1 e2) NumType"
    | tc_cat [simp]: "typecheck gam e1 StrType ==> typecheck gam e2 StrType ==>
                    typecheck gam (Cat e1 e2) StrType"
    | tc_len [simp]: "typecheck gam e StrType ==> typecheck gam (Len e) NumType"
    | tc_let [simp]: "typecheck gam e1 t1 ==> typecheck (extend gam t1) e2 t2 ==> 
                    typecheck gam (Let e1 e2) t2"
    | tc_lam [simp]: "typecheck (extend gam t1) e t2 ==> typecheck gam (Lam t1 e) (Arrow t1 t2)"
    | tc_appl [simp]: "typecheck gam e1 (Arrow t2 t) ==> typecheck gam e2 t2 ==> 
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

lemma [simp]: "typecheck gam e t ==> n in gam ==> 
         typecheck (extend_at n gam t') (insert n e) t"
by (induction gam e t arbitrary: n rule: typecheck.induct, fastforce+)

lemma [simp]: "typecheck (extend_at n gam t') e t ==> n in gam ==> typecheck gam e' t' ==> 
        typecheck gam (remove n (subst' n (insert n e') e)) t"
by (induction "extend_at n gam t'" e t arbitrary: n gam t' e' rule: typecheck.induct, fastforce+)

lemma [simp]: "typecheck (extend gam t') e t ==> typecheck gam e' t' ==> 
                          typecheck gam (subst e' n e) t"
by (simp add: subst_def)

end
