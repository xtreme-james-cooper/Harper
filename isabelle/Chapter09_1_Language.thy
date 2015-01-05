theory Chapter09_1_Language
imports DeBruijnEnvironment
begin

datatype type = 
  Nat
| Arrow type type

datatype expr = 
  Var var
| Zero
| Suc expr
| Rec expr expr expr
| Lam type expr
| Appl expr expr

primrec insert :: "var => expr => expr"
where "insert n (Var v) = Var (incr n v)"
    | "insert n Zero = Zero"
    | "insert n (Suc e) = Suc (insert n e)"
    | "insert n (Rec et e0 es) = Rec (insert n et) (insert n e0) (insert (next (next n)) es)"
    | "insert n (Lam t e) = Lam t (insert (next n) e)"
    | "insert n (Appl e1 e2) = Appl (insert n e1) (insert n e2)"

primrec remove :: "var => expr => expr"
where "remove n (Var v) = Var (subr n v)"
    | "remove n Zero = Zero"
    | "remove n (Suc e) = Suc (remove n e)"
    | "remove n (Rec et e0 es) = Rec (remove n et) (remove n e0) (remove (next (next n)) es)"
    | "remove n (Lam t e) = Lam t (remove (next n) e)"
    | "remove n (Appl e1 e2) = Appl (remove n e1) (remove n e2)"

primrec subst' :: "var => expr => expr => expr"
where "subst' n e' (Var v) = (if v = n then e' else Var v)"
    | "subst' n e' Zero = Zero"
    | "subst' n e' (Suc e) = Suc (subst' n e' e)"
    | "subst' n e' (Rec et e0 es) = 
                      Rec (subst' n e' et) (subst' n e' e0) 
                          (subst' (next (next n)) (insert first (insert first e')) es)"
    | "subst' n e' (Lam t e) = Lam t (subst' (next n) (insert first e') e)"
    | "subst' n e' (Appl e1 e2) = Appl (subst' n e' e1) (subst' n e' e2)"

definition subst :: "expr => var => expr => expr"
where "subst e' n e = remove first (subst' first (insert first e') e)"

lemma [simp]: "remove n (insert n e) = e"
by (induction e arbitrary: n, simp_all)

lemma [simp]: "canswap m n ==> insert m (insert n e) = insert (next n) (insert m e)"
by (induction e arbitrary: n m, simp_all)

end
