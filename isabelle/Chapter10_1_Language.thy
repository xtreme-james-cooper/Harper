theory Chapter10_1_Language
imports DeBruijnEnvironment
begin

datatype type = 
  Nat
| Arrow type type
| Unit
| Prod type type

datatype expr = 
  Var var
| Zero
| Suc expr
| Rec expr expr expr
| Lam type expr
| Appl expr expr
| Triv
| Pair expr expr
| ProjL expr
| ProjR expr

primrec insert :: "var => expr => expr"
where "insert n (Var v) = Var (incr n v)"
    | "insert n Zero = Zero"
    | "insert n (Suc e) = Suc (insert n e)"
    | "insert n (Rec et e0 es) = Rec (insert n et) (insert n e0) (insert (next (next n)) es)"
    | "insert n (Lam t e) = Lam t (insert (next n) e)"
    | "insert n (Appl e1 e2) = Appl (insert n e1) (insert n e2)"
    | "insert n Triv = Triv"
    | "insert n (Pair e1 e2) = Pair (insert n e1) (insert n e2)"
    | "insert n (ProjL e) = ProjL (insert n e)"
    | "insert n (ProjR e) = ProjR (insert n e)"

primrec subst :: "expr => var => expr => expr"
where "subst e' n (Var v) = (if v = n then e' else Var (subr n v))"
    | "subst e' n Zero = Zero"
    | "subst e' n (Suc e) = Suc (subst e' n e)"
    | "subst e' n (Rec et e0 es) = 
                      Rec (subst e' n et) (subst e' n e0) 
                          (subst (insert first (insert first e')) (next (next n)) es)"
    | "subst e' n (Lam t e) = Lam t (subst (insert first e') (next n) e)"
    | "subst e' n (Appl e1 e2) = Appl (subst e' n e1) (subst e' n e2)"
    | "subst e' n Triv = Triv"
    | "subst e' n (Pair e1 e2) = Pair (subst e' n e1) (subst e' n e2)"
    | "subst e' n (ProjL e) = ProjL (subst e' n e)"
    | "subst e' n (ProjR e) = ProjR (subst e' n e)"

lemma [simp]: "canswap m n ==> insert m (insert n e) = insert (next n) (insert m e)"
by (induction e arbitrary: n m, simp_all)

end
