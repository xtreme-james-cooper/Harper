theory Chapter08_1_Language
imports DeBruijnEnvironment
begin

datatype type = 
  NumType 
| StrType
| Arrow type type

datatype expr = 
  Var var
| Num int
| Str string
| Plus expr expr
| Times expr expr
| Cat expr expr
| Len expr
| Let expr expr
| Lam type expr
| Appl expr expr

primrec insert :: "var => expr => expr"
where "insert n (Var v) = Var (incr n v)"
    | "insert n (Num x) = Num x"
    | "insert n (Str s) = Str s"
    | "insert n (Plus e1 e2) = Plus (insert n e1) (insert n e2)"
    | "insert n (Times e1 e2) = Times (insert n e1) (insert n e2)"
    | "insert n (Cat e1 e2) = Cat (insert n e1) (insert n e2)"
    | "insert n (Len e) = Len (insert n e)"
    | "insert n (Let e1 e2) = Let (insert n e1) (insert (next n) e2)"
    | "insert n (Lam t e) = Lam t (insert (next n) e)"
    | "insert n (Appl e1 e2) = Appl (insert n e1) (insert n e2)"

primrec subst :: "expr => var => expr => expr"
where "subst e' n (Var x) = (if x = n then e' else Var (subr n x))"
    | "subst e' n (Num x) = Num x"
    | "subst e' n (Str s) = Str s"
    | "subst e' n (Plus e1 e2) = Plus (subst e' n e1) (subst e' n e2)"
    | "subst e' n (Times e1 e2) = Times (subst e' n e1) (subst e' n e2)"
    | "subst e' n (Cat e1 e2) = Cat (subst e' n e1) (subst e' n e2)"
    | "subst e' n (Len e) = Len (subst e' n e)"
    | "subst e' n (Let e1 e2) = Let (subst e' n e1) (subst (insert first e') (next n) e2)"
    | "subst e' n (Lam t e) = Lam t (subst (insert first e') (next n) e)"
    | "subst e' n (Appl e1 e2) = Appl (subst e' n e1) (subst e' n e2)"

end
