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

primrec insert :: "var => expr => expr"
where "insert n (Var v) = Var (incr n v)"
    | "insert n (Num x) = Num x"
    | "insert n (Str s) = Str s"
    | "insert n (Plus e1 e2) = Plus (insert n e1) (insert n e2)"
    | "insert n (Times e1 e2) = Times (insert n e1) (insert n e2)"
    | "insert n (Cat e1 e2) = Cat (insert n e1) (insert n e2)"
    | "insert n (Len e) = Len (insert n e)"
    | "insert n (Let e1 e2) = Let (insert n e1) (insert (next n) e2)"

primrec subst :: "expr => var => expr => expr"
where "subst e' n (Var x) = (if x = n then e' else Var (subr n x))"
    | "subst e' n (Num x) = Num x"
    | "subst e' n (Str s) = Str s"
    | "subst e' n (Plus e1 e2) = Plus (subst e' n e1) (subst e' n e2)"
    | "subst e' n (Times e1 e2) = Times (subst e' n e1) (subst e' n e2)"
    | "subst e' n (Cat e1 e2) = Cat (subst e' n e1) (subst e' n e2)"
    | "subst e' n (Len e) = Len (subst e' n e)"
    | "subst e' n (Let e1 e2) = Let (subst e' n e1) (subst (insert first e') (next n) e2)"

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

lemma [simp]: "typecheck gam e t ==> n in gam ==> typecheck (extend_at n gam t') (insert n e) t"
by (induction gam e t arbitrary: n rule: typecheck.induct, simp_all add: insert_def, fastforce+)

lemma [simp]: "typecheck (extend_at n gam t') e t ==> n in gam ==> typecheck gam e' t' ==> 
                          typecheck gam (subst e' n e) t"
by (induction "extend_at n gam t'" e t arbitrary: gam e' n rule: typecheck.induct, fastforce+)

end
