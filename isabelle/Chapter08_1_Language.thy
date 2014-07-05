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

primrec remove :: "var => expr => expr"
where "remove n (Var v) = Var (subr n v)"
    | "remove n (Num x) = Num x"
    | "remove n (Str s) = Str s"
    | "remove n (Plus e1 e2) = Plus (remove n e1) (remove n e2)"
    | "remove n (Times e1 e2) = Times (remove n e1) (remove n e2)"
    | "remove n (Cat e1 e2) = Cat (remove n e1) (remove n e2)"
    | "remove n (Len e) = Len (remove n e)"
    | "remove n (Let e1 e2) = Let (remove n e1) (remove (next n) e2)"
    | "remove n (Lam t e) = Lam t (remove (next n) e)"
    | "remove n (Appl e1 e2) = Appl (remove n e1) (remove n e2)"

primrec subst' :: "var => expr => expr => expr"
where "subst' n e' (Var v) = (if v = n then e' else Var v)"
    | "subst' n e' (Num x) = Num x"
    | "subst' n e' (Str s) = Str s"
    | "subst' n e' (Plus e1 e2) = Plus (subst' n e' e1) (subst' n e' e2)"
    | "subst' n e' (Times e1 e2) = Times (subst' n e' e1) (subst' n e' e2)"
    | "subst' n e' (Cat e1 e2) = Cat (subst' n e' e1) (subst' n e' e2)"
    | "subst' n e' (Len e) = Len (subst' n e' e)"
    | "subst' n e' (Let e1 e2) = Let (subst' n e' e1) (subst' (next n) (insert first e') e2)"
    | "subst' n e' (Lam t e) = Lam t (subst' (next n) (insert first e') e)"
    | "subst' n e' (Appl e1 e2) = Appl (subst' n e' e1) (subst' n e' e2)"

definition subst :: "expr => expr => expr"
where "subst e' e = remove first (subst' first (insert first e') e)"

lemma [simp]: "remove n (insert n e) = e"
by (induction e arbitrary: n, simp_all)

lemma [simp]: "canswap m n ==> insert m (insert n e) = insert (next n) (insert m e)"
by (induction e arbitrary: n m, simp_all)

end
