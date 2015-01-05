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

primrec subst :: "expr => var => expr => expr"
where "subst e' n (Var v) = (if v = n then e' else Var (subr n v))"
    | "subst e' n (Num x) = Num x"
    | "subst e' n Zero = Zero"
    | "subst e' n (Succ e) = Succ (subst e' n e)"
    | "subst e' n (IsZ et e0 es) = 
                      IsZ (subst e' n et) (subst e' n e0) (subst (insert first e') (next n) es)"
    | "subst e' n (Lam e) = Lam (subst (insert first e') (next n) e)"
    | "subst e' n (Appl e1 e2) = Appl (subst e' n e1) (subst e' n e2)"
    | "subst e' n (Fix e) = Fix (subst (insert first e') (next n) e)"

lemma [simp]: "canswap m n ==> insert m (insert n e) = insert (next n) (insert m e)"
by (induction e arbitrary: n m, simp_all)

end
