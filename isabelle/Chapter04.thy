theory Chapter04
imports DeBruijnEnvironment
begin

datatype type = NumType | StrType

datatype expr = 
  Var nat
| Num int
| Str string
| Plus expr expr
| Times expr expr
| Cat expr expr
| Len expr
| Let expr expr

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

inductive_cases [elim!]: "typecheck gam (Var x) t"
inductive_cases [elim!]: "typecheck gam (Str s) t"
inductive_cases [elim!]: "typecheck gam (Num n) t"
inductive_cases [elim!]: "typecheck gam (Plus e1 e2) t"
inductive_cases [elim!]: "typecheck gam (Times e1 e2) t"
inductive_cases [elim!]: "typecheck gam (Cat e1 e2) t"
inductive_cases [elim!]: "typecheck gam (Len e) t"
inductive_cases [elim!]: "typecheck gam (Let e1 e2) t"

primrec incr_from :: "nat => expr => expr"
where "incr_from n (Var v) = Var (if v < n then v else Suc v)"
    | "incr_from n (Num x) = Num x"
    | "incr_from n (Str s) = Str s"
    | "incr_from n (Plus e1 e2) = Plus (incr_from n e1) (incr_from n e2)"
    | "incr_from n (Times e1 e2) = Times (incr_from n e1) (incr_from n e2)"
    | "incr_from n (Cat e1 e2) = Cat (incr_from n e1) (incr_from n e2)"
    | "incr_from n (Len e) = Len (incr_from n e)"
    | "incr_from n (Let e1 e2) = Let (incr_from n e1) (incr_from (Suc n) e2)"

primrec sub_from :: "nat => expr => expr"
where "sub_from n (Var v) = Var (if v < n then v else v - 1)"
    | "sub_from n (Num x) = Num x"
    | "sub_from n (Str s) = Str s"
    | "sub_from n (Plus e1 e2) = Plus (sub_from n e1) (sub_from n e2)"
    | "sub_from n (Times e1 e2) = Times (sub_from n e1) (sub_from n e2)"
    | "sub_from n (Cat e1 e2) = Cat (sub_from n e1) (sub_from n e2)"
    | "sub_from n (Len e) = Len (sub_from n e)"
    | "sub_from n (Let e1 e2) = Let (sub_from n e1) (sub_from (Suc n) e2)"

primrec subst' :: "nat => expr => expr => expr"
where "subst' n e' (Var v) = (if v = n then e' else Var v)"
    | "subst' n e' (Num x) = Num x"
    | "subst' n e' (Str s) = Str s"
    | "subst' n e' (Plus e1 e2) = Plus (subst' n e' e1) (subst' n e' e2)"
    | "subst' n e' (Times e1 e2) = Times (subst' n e' e1) (subst' n e' e2)"
    | "subst' n e' (Cat e1 e2) = Cat (subst' n e' e1) (subst' n e' e2)"
    | "subst' n e' (Len e) = Len (subst' n e' e)"
    | "subst' n e' (Let e1 e2) = Let (subst' n e' e1) (subst' (Suc n) (incr_from 0 e') e2)"

definition subst :: "expr => expr => expr"
where "subst e' e = sub_from 0 (subst' 0 (incr_from 0 e') e)"

primrec free_vars :: "expr => nat set"
where "free_vars (Var v) = {v}"
    | "free_vars (Num x) = {}"
    | "free_vars (Str s) = {}"
    | "free_vars (Plus e1 e2) = free_vars e1 Un free_vars e2"
    | "free_vars (Times e1 e2) = free_vars e1 Un free_vars e2"
    | "free_vars (Cat e1 e2) = free_vars e1 Un free_vars e2"
    | "free_vars (Len e) = free_vars e"
    | "free_vars (Let e1 e2) = free_vars e1 Un (%x. x - 1) ` (free_vars e2 - {0})"

lemma [simp]: "typecheck gam e t ==> n <= size gam ==> 
         typecheck (extend_at n gam t') (incr_from n e) t"
proof (induction gam e t arbitrary: n rule: typecheck.induct)
case (tc_var x t)
  thus ?case by simp
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
  from tc_let have X: "typecheck (extend_at n gam t') (incr_from n e1) t1" by simp
  from tc_let have "typecheck (extend (extend_at n gam t') t1) (incr_from (Suc n) e2) t2" by simp
  with X show ?case by simp
qed

lemma [simp]: "sub_from n (incr_from n e) = e"
by (induction e arbitrary: n, simp_all)

lemma [simp]: "m <= n ==> incr_from m (incr_from n e) = incr_from (Suc n) (incr_from m e)"
by (induction e arbitrary: n m, simp_all)

lemma [simp]: "typecheck (extend_at n gam t') e t ==> n <= size gam ==> typecheck gam e' t' ==> 
        typecheck gam (sub_from n (subst' n (incr_from n e') e)) t"
proof (induction "extend_at n gam t'" e t arbitrary: n gam t' e' rule: typecheck.induct)
case (tc_var x t)
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
next case (tc_let e1 t1 e2 t2 n)
  with tc_let have X: "typecheck (extend gam t1) (sub_from (Suc n) (subst' (Suc n) 
                             (incr_from (Suc n) (incr_from 0 e')) e2)) t2" by simp
  from tc_let have "typecheck gam (sub_from n (subst' n (incr_from n e') e1)) t1" by simp
  with X show ?case by simp
qed

lemma [simp]: "typecheck (extend gam t') e t ==> typecheck gam e' t' ==> 
                          typecheck gam (subst e' e) t"
by (simp add: subst_def)

end
