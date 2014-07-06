theory Chapter16_2_Expression
imports Chapter16_1_Type
begin

datatype expr = 
  Var var
| Zero
| Suc expr
| IsZ expr expr expr
| Lam type expr
| Appl expr expr
| Triv
| Pair expr expr
| ProjL expr
| ProjR expr
| Abort type expr
| Case expr expr expr
| InL type type expr
| InR type type expr
| Fix type expr

primrec insert :: "var => expr => expr"
where "insert n (Var v) = Var (incr n v)"
    | "insert n Zero = Zero"
    | "insert n (Suc e) = Suc (insert n e)"
    | "insert n (IsZ et e0 es) = IsZ (insert n et) (insert n e0) (insert (next n) es)"
    | "insert n (Lam t e) = Lam t (insert (next n) e)"
    | "insert n (Appl e1 e2) = Appl (insert n e1) (insert n e2)"
    | "insert n Triv = Triv"
    | "insert n (Pair e1 e2) = Pair (insert n e1) (insert n e2)"
    | "insert n (ProjL e) = ProjL (insert n e)"
    | "insert n (ProjR e) = ProjR (insert n e)"
    | "insert n (Abort t e) = Abort t (insert n e)"
    | "insert n (Case et el er) = Case (insert n et) (insert (next n) el) (insert (next n) er)"
    | "insert n (InL t1 t2 e) = InL t1 t2 (insert n e)"
    | "insert n (InR t1 t2 e) = InR t1 t2 (insert n e)"
    | "insert n (Fix t e) = Fix t (insert (next n) e)"

primrec remove :: "var => expr => expr"
where "remove n (Var v) = Var (subr n v)"
    | "remove n Zero = Zero"
    | "remove n (Suc e) = Suc (remove n e)"
    | "remove n (IsZ et e0 es) = IsZ (remove n et) (remove n e0) (remove (next n) es)"
    | "remove n (Lam t e) = Lam t (remove (next n) e)"
    | "remove n (Appl e1 e2) = Appl (remove n e1) (remove n e2)"
    | "remove n Triv = Triv"
    | "remove n (Pair e1 e2) = Pair (remove n e1) (remove n e2)"
    | "remove n (ProjL e) = ProjL (remove n e)"
    | "remove n (ProjR e) = ProjR (remove n e)"
    | "remove n (Abort t e) = Abort t (remove n e)"
    | "remove n (Case et el er) = Case (remove n et) (remove (next n) el) (remove (next n) er)"
    | "remove n (InL t1 t2 e) = InL t1 t2 (remove n e)"
    | "remove n (InR t1 t2 e) = InR t1 t2 (remove n e)"
    | "remove n (Fix t e) = Fix t (remove (next n) e)"

primrec subst' :: "var => expr => expr => expr"
where "subst' n e' (Var v) = (if v = n then e' else Var v)"
    | "subst' n e' Zero = Zero"
    | "subst' n e' (Suc e) = Suc (subst' n e' e)"
    | "subst' n e' (IsZ et e0 es) = 
                      IsZ (subst' n e' et) (subst' n e' e0) (subst' (next n) (insert first e') es)"
    | "subst' n e' (Lam t e) = Lam t (subst' (next n) (insert first e') e)"
    | "subst' n e' (Appl e1 e2) = Appl (subst' n e' e1) (subst' n e' e2)"
    | "subst' n e' Triv = Triv"
    | "subst' n e' (Pair e1 e2) = Pair (subst' n e' e1) (subst' n e' e2)"
    | "subst' n e' (ProjL e) = ProjL (subst' n e' e)"
    | "subst' n e' (ProjR e) = ProjR (subst' n e' e)"
    | "subst' n e' (Abort t e) = Abort t (subst' n e' e)"
    | "subst' n e' (Case et el er) = 
                      Case (subst' n e' et) 
                           (subst' (next n) (insert first e') el) 
                           (subst' (next n) (insert first e') er)"
    | "subst' n e' (InL t1 t2 e) = InL t1 t2 (subst' n e' e)"
    | "subst' n e' (InR t1 t2 e) = InR t1 t2 (subst' n e' e)"
    | "subst' n e' (Fix t e) = Fix t (subst' (next n) (insert first e') e)"

definition subst :: "expr => expr => expr"
where "subst e' e = remove first (subst' first (insert first e') e)"

lemma [simp]: "remove n (insert n e) = e"
by (induction e arbitrary: n, simp_all)

lemma [simp]: "canswap m n ==> insert m (insert n e) = insert (next n) (insert m e)"
by (induction e arbitrary: n m, simp_all)

end
