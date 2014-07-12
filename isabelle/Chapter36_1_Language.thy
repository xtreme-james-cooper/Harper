theory Chapter36_1_Language
imports DeBruijnEnvironment
begin

datatype type = 
  Nat
| Arrow type type
| Unit
| Prod type type
| Void
| Sum type type
| Command type

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
| Cmd cmnd
and cmnd =
  Return expr
| Bind expr cmnd
| Declare expr cmnd
| Get var
| Set var expr

primrec insert :: "var => expr => expr"
    and insert_cmd :: "var => cmnd => cmnd"
where "insert n (Var v) = Var (incr n v)"
    | "insert n Zero = Zero"
    | "insert n (Suc e) = Suc (insert n e)"
    | "insert n (IsZ et e0 es) = 
            IsZ (insert n et) (insert n e0) (insert (next n) es)"
    | "insert n (Lam t e) = Lam t (insert (next n) e)"
    | "insert n (Appl e1 e2) = Appl (insert n e1) (insert n e2)"
    | "insert n Triv = Triv"
    | "insert n (Pair e1 e2) = Pair (insert n e1) (insert n e2)"
    | "insert n (ProjL e) = ProjL (insert n e)"
    | "insert n (ProjR e) = ProjR (insert n e)"
    | "insert n (Abort t e) = Abort t (insert n e)"
    | "insert n (Case et el er) = 
            Case (insert n et) (insert (next n) el) (insert (next n) er)"
    | "insert n (InL t1 t2 e) = InL t1 t2 (insert n e)"
    | "insert n (InR t1 t2 e) = InR t1 t2 (insert n e)"
    | "insert n (Fix t e) = Fix t (insert (next n) e)"
    | "insert n (Cmd c) = Cmd (insert_cmd n c)"
    | "insert_cmd n (Return e) = Return (insert n e)"
    | "insert_cmd n (Bind e c) = Bind (insert n e) (insert_cmd (next n) c)"
    | "insert_cmd n (Declare e c) = Declare (insert n e) (insert_cmd n c)"
    | "insert_cmd n (Get v) = Get v"
    | "insert_cmd n (Set v e) = Set v (insert n e)"

primrec remove :: "var => expr => expr"
    and remove_cmd :: "var => cmnd => cmnd"
where "remove n (Var v) = Var (subr n v)"
    | "remove n Zero = Zero"
    | "remove n (Suc e) = Suc (remove n e)"
    | "remove n (IsZ et e0 es) = 
            IsZ (remove n et) (remove n e0) (remove (next n) es)"
    | "remove n (Lam t e) = Lam t (remove (next n) e)"
    | "remove n (Appl e1 e2) = Appl (remove n e1) (remove n e2)"
    | "remove n Triv = Triv"
    | "remove n (Pair e1 e2) = Pair (remove n e1) (remove n e2)"
    | "remove n (ProjL e) = ProjL (remove n e)"
    | "remove n (ProjR e) = ProjR (remove n e)"
    | "remove n (Abort t e) = Abort t (remove n e)"
    | "remove n (Case et el er) = 
            Case (remove n et) (remove (next n) el) (remove (next n) er)"
    | "remove n (InL t1 t2 e) = InL t1 t2 (remove n e)"
    | "remove n (InR t1 t2 e) = InR t1 t2 (remove n e)"
    | "remove n (Fix t e) = Fix t (remove (next n) e)"
    | "remove n (Cmd c) = Cmd (remove_cmd n c)"
    | "remove_cmd n (Return e) = Return (remove n e)"
    | "remove_cmd n (Bind e c) = Bind (remove n e) (remove_cmd (next n) c)"
    | "remove_cmd n (Declare e c) = Declare (remove n e) (remove_cmd n c)"
    | "remove_cmd n (Get v) = Get v"
    | "remove_cmd n (Set v e) = Set v (remove n e)"

primrec subst' :: "var => expr => expr => expr"
    and subst_cmd' :: "var => expr => cmnd => cmnd"
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
    | "subst' n e' (Cmd c) = Cmd (subst_cmd' n e' c)"
    | "subst_cmd' n e' (Return e) = Return (subst' n e' e)"
    | "subst_cmd' n e' (Bind e c) = Bind (subst' n e' e) (subst_cmd' (next n) (insert first e') c)"
    | "subst_cmd' n e' (Declare e c) = Declare (subst' n e' e) (subst_cmd' n e' c)"
    | "subst_cmd' n e' (Get v) = Get v"
    | "subst_cmd' n e' (Set v e) = Set v (subst' n e' e)"

definition subst :: "expr => expr => expr"
where "subst e' e = remove first (subst' first (insert first e') e)"

definition subst_cmd :: "expr => cmnd => cmnd"
where "subst_cmd e' c = remove_cmd first (subst_cmd' first (insert first e') c)"

lemma [simp]: "remove n (insert n e) = e"
  and [simp]: "remove_cmd n (insert_cmd n c) = c"
by (induction e and c arbitrary: n and n, simp_all)

lemma [simp]: "canswap m n ==> insert m (insert n e) = insert (next n) (insert m e)"
  and [simp]: "canswap m n ==> insert_cmd m (insert_cmd n c) = insert_cmd (next n) (insert_cmd m c)"
by (induction e and c arbitrary: n m and n m, simp_all)

lemma [simp]: "canswap m n ==> insert m (remove n e) = remove (next n) (insert m e)"
  and [simp]: "canswap m n ==> insert_cmd m (remove_cmd n c) = remove_cmd (next n) (insert_cmd m c)"
by (induction e and c arbitrary: n m and n m, simp_all)

lemma [simp]: "canswap m n ==> insert m (subst' n e' e) = subst' (next n) (insert m e') (insert m e)"
  and [simp]: "canswap m n ==> insert_cmd m (subst_cmd' n e' c) = subst_cmd' (next n) (insert m e') (insert_cmd m c)"
by (induction e and c arbitrary: n m e' and n m e', simp_all)

end
