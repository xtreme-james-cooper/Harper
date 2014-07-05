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

primrec insert :: "var => expr => expr"
where "insert n (Var v) = Var (incr n v)"
    | "insert n (Num x) = Num x"
    | "insert n (Str s) = Str s"
    | "insert n (Plus e1 e2) = Plus (insert n e1) (insert n e2)"
    | "insert n (Times e1 e2) = Times (insert n e1) (insert n e2)"
    | "insert n (Cat e1 e2) = Cat (insert n e1) (insert n e2)"
    | "insert n (Len e) = Len (insert n e)"
    | "insert n (Let e1 e2) = Let (insert n e1) (insert (next n) e2)"

primrec remove :: "var => expr => expr"
where "remove n (Var v) = Var (subr n v)"
    | "remove n (Num x) = Num x"
    | "remove n (Str s) = Str s"
    | "remove n (Plus e1 e2) = Plus (remove n e1) (remove n e2)"
    | "remove n (Times e1 e2) = Times (remove n e1) (remove n e2)"
    | "remove n (Cat e1 e2) = Cat (remove n e1) (remove n e2)"
    | "remove n (Len e) = Len (remove n e)"
    | "remove n (Let e1 e2) = Let (remove n e1) (remove (next n) e2)"

primrec subst' :: "var => expr => expr => expr"
where "subst' n e' (Var v) = (if v = n then e' else Var v)"
    | "subst' n e' (Num x) = Num x"
    | "subst' n e' (Str s) = Str s"
    | "subst' n e' (Plus e1 e2) = Plus (subst' n e' e1) (subst' n e' e2)"
    | "subst' n e' (Times e1 e2) = Times (subst' n e' e1) (subst' n e' e2)"
    | "subst' n e' (Cat e1 e2) = Cat (subst' n e' e1) (subst' n e' e2)"
    | "subst' n e' (Len e) = Len (subst' n e' e)"
    | "subst' n e' (Let e1 e2) = Let (subst' n e' e1) (subst' (next n) (insert first e') e2)"

definition subst :: "expr => expr => expr"
where "subst e' e = remove first (subst' first (insert first e') e)"

lemma [simp]: "typecheck gam e t ==> n in gam ==> 
         typecheck (extend_at n gam t') (insert n e) t"
by (induction gam e t arbitrary: n rule: typecheck.induct, fastforce+)

lemma [simp]: "remove n (insert n e) = e"
by (induction e arbitrary: n, simp_all)

lemma [simp]: "canswap m n ==> insert m (insert n e) = insert (next n) (insert m e)"
by (induction e arbitrary: n m, simp_all)

lemma [simp]: "typecheck (extend_at n gam t') e t ==> n in gam ==> typecheck gam e' t' ==> 
        typecheck gam (remove n (subst' n (insert n e') e)) t"
by (induction "extend_at n gam t'" e t arbitrary: n gam t' e' rule: typecheck.induct, fastforce+)

lemma [simp]: "typecheck (extend gam t') e t ==> typecheck gam e' t' ==> 
                          typecheck gam (subst e' e) t"
by (simp add: subst_def)

end
