theory Chapter04
imports DeBruijnEnvironment
begin

datatype type = NumType | StrType

datatype expr = 
  Var var
| Num int
| Str string
| Plus expr expr
| Times expr expr
| Cat expr expr
| Len expr
| Let expr expr

primrec expr_map :: "(var => var => expr) => 
                      ((var => var => expr) => (var => var => expr)) => var => expr => expr"
where "expr_map f c n (Var v) = f n v"
    | "expr_map f c n (Num x) = Num x"
    | "expr_map f c n (Str s) = Str s"
    | "expr_map f c n (Plus e1 e2) = Plus (expr_map f c n e1) (expr_map f c n e2)"
    | "expr_map f c n (Times e1 e2) = Times (expr_map f c n e1) (expr_map f c n e2)"
    | "expr_map f c n (Cat e1 e2) = Cat (expr_map f c n e1) (expr_map f c n e2)"
    | "expr_map f c n (Len e) = Len (expr_map f c n e)"
    | "expr_map f c n (Let e1 e2) = Let (expr_map f c n e1) (expr_map (c f) c (next n) e2)"

definition insert :: "var => expr => expr"
where "insert = expr_map (%n. Var o incr n) id"

definition remove :: "var => expr => expr"
where "remove = expr_map (%n. Var o subr n) id"

definition subst' :: "expr => var => expr => expr"
where "subst' e' = expr_map (%n v. if v = n then e' else Var v) 
                            (%f n v. if v = n then insert first (f n v) else f n v)"

definition subst :: "expr => var => expr => expr"
where "subst e' n e = remove n (subst' (insert n e') n e)"

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

lemma [simp]: "remove n (insert n e) = e"
by (induction e arbitrary: n, simp_all add: insert_def remove_def)

lemma [simp]: "canswap m n ==> insert m (insert n e) = insert (next n) (insert m e)"
by (induction e arbitrary: n m, simp_all add: insert_def)

lemma [simp]: "(%m v. if v = m then insert first (if v = m then insert n e else Var v) 
                      else if v = m then insert n e 
                      else Var v) =
               (%m v. if v = m then insert (next n) (insert first e) 
                      else Var v)"
proof -
  have "ALL m v. (%m v. if v = m then insert first (if v = m then insert n e else Var v) 
                      else if v = m then insert n e 
                      else Var v) m v =
               (%m v. if v = m then insert (next n) (insert first e) 
                      else Var v) m v" by simp
  thus ?thesis by simp
qed

lemma [simp]: "subst e' n (Var x) = (if x = n then e' else Var (subr n x))"
proof (cases "x = n")
case True
  thus ?thesis by (simp add: subst_def subst'_def)
next case False
  thus ?thesis by (simp add: remove_def subst_def subst'_def)
qed

lemma [simp]: "subst e' n (Str x) = Str x"
by (simp add: remove_def subst_def subst'_def)

lemma [simp]: "subst e' n (Num x) = Num x"
by (simp add: remove_def subst_def subst'_def)

lemma [simp]: "subst e' n (Plus e1 e2) = Plus (subst e' n e1) (subst e' n e2)"
by (simp add: remove_def subst_def subst'_def)

lemma [simp]: "subst e' n (Times e1 e2) = Times (subst e' n e1) (subst e' n e2)"
by (simp add: remove_def subst_def subst'_def)

lemma [simp]: "subst e' n (Cat e1 e2) = Cat (subst e' n e1) (subst e' n e2)"
by (simp add: remove_def subst_def subst'_def)

lemma [simp]: "subst e' n (Len e) = Len (subst e' n e)"
by (simp add: remove_def subst_def subst'_def)

lemma [simp]: "subst e' n (Let e1 e2) = Let (subst e' n e1) (subst (insert first e') (next n) e2)"
by (simp add: subst_def subst'_def remove_def)

lemma [simp]: "typecheck gam e t ==> n in gam ==> typecheck (extend_at n gam t') (insert n e) t"
proof (induction gam e t arbitrary: n rule: typecheck.induct)
case tc_var
  thus ?case by (simp add: insert_def)
next case tc_str
  thus ?case by (simp add: insert_def)
next case tc_num
  thus ?case by (simp add: insert_def)
next case tc_plus
  thus ?case by (simp add: insert_def)
next case tc_times
  thus ?case by (simp add: insert_def)
next case tc_cat
  thus ?case by (simp add: insert_def)
next case tc_len
  thus ?case by (simp add: insert_def)
next case (tc_let gam e1 t1 e2 t2)
  hence "typecheck (extend_at first (extend_at n gam t') t1) (insert (next n) e2) t2" by simp
  moreover from tc_let have "typecheck (extend_at n gam t') (insert n e1) t1" by simp
  ultimately show ?case by (simp add: insert_def)
qed

lemma [simp]: "typecheck (extend_at n gam t') e t ==> n in gam ==> typecheck gam e' t' ==> 
                          typecheck gam (subst e' n e) t"
proof (induction "extend_at n gam t'" e t arbitrary: gam e' n rule: typecheck.induct)
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
  hence "typecheck (extend gam t1) (subst (insert first e') (next n) e2) t2" by simp
  moreover from tc_let have "typecheck gam (subst e' n e1) t1" by simp 
  ultimately show ?case by simp
qed

end
