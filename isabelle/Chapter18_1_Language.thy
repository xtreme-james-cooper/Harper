theory Chapter18_1_Language
imports DeBruijnEnvironment
begin

datatype expr = 
  Var var
| Num nat
| Zero
| Succ expr
| IsZ expr expr expr
| Lam expr
| Appl expr expr
| Fix expr

primrec insert :: "var => expr => expr"
where "insert n (Var v) = Var (incr n v)"
    | "insert n (Num x) = Num x"
    | "insert n Zero = Zero"
    | "insert n (Succ e) = Succ (insert n e)"
    | "insert n (IsZ et e0 es) = IsZ (insert n et) (insert n e0) (insert (next n) es)"
    | "insert n (Lam e) = Lam (insert (next n) e)"
    | "insert n (Appl e1 e2) = Appl (insert n e1) (insert n e2)"
    | "insert n (Fix e) = Fix (insert (next n) e)"

primrec remove :: "var => expr => expr"
where "remove n (Var v) = Var (subr n v)"
    | "remove n (Num x) = Num x"
    | "remove n Zero = Zero"
    | "remove n (Succ e) = Succ (remove n e)"
    | "remove n (IsZ et e0 es) = IsZ (remove n et) (remove n e0) (remove (next n) es)"
    | "remove n (Lam e) = Lam (remove (next n) e)"
    | "remove n (Appl e1 e2) = Appl (remove n e1) (remove n e2)"
    | "remove n (Fix e) = Fix (remove (next n) e)"

primrec subst' :: "var => expr => expr => expr"
where "subst' n e' (Var v) = (if v = n then e' else Var v)"
    | "subst' n e' (Num x) = Num x"
    | "subst' n e' Zero = Zero"
    | "subst' n e' (Succ e) = Succ (subst' n e' e)"
    | "subst' n e' (IsZ et e0 es) = 
                      IsZ (subst' n e' et) (subst' n e' e0) (subst' (next n) (insert first e') es)"
    | "subst' n e' (Lam e) = Lam (subst' (next n) (insert first e') e)"
    | "subst' n e' (Appl e1 e2) = Appl (subst' n e' e1) (subst' n e' e2)"
    | "subst' n e' (Fix e) = Fix (subst' (next n) (insert first e') e)"

definition subst :: "expr => var => expr => expr"
where "subst e' n e = remove first (subst' first (insert first e') e)"

lemma [simp]: "remove n (insert n e) = e"
by (induction e arbitrary: n, simp_all)

lemma [simp]: "canswap m n ==> insert m (insert n e) = insert (next n) (insert m e)"
by (induction e arbitrary: n m, simp_all)

end
