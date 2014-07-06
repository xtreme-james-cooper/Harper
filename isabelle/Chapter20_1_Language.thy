theory Chapter20_1_Language
imports DeBruijnEnvironment
begin

datatype type = 
  Tyvar var
| Nat
| Arrow type type
| All type
| Unit
| Prod type type
| Void
| Sum type type

primrec type_insert :: "var => type => type"
where "type_insert n (Tyvar v) = Tyvar (incr n v)"
    | "type_insert n Nat = Nat"
    | "type_insert n (Arrow e1 e2) = Arrow (type_insert n e1) (type_insert n e2)"
    | "type_insert n (All e) = All (type_insert (next n) e)"
    | "type_insert n Unit = Unit"
    | "type_insert n (Prod e1 e2) = Prod (type_insert n e1) (type_insert n e2)"
    | "type_insert n Void = Void"
    | "type_insert n (Sum e1 e2) = Sum (type_insert n e1) (type_insert n e2)"

primrec type_remove :: "var => type => type"
where "type_remove n (Tyvar v) = Tyvar (subr n v)"
    | "type_remove n Nat = Nat"
    | "type_remove n (Arrow e1 e2) = Arrow (type_remove n e1) (type_remove n e2)"
    | "type_remove n (All e) = All (type_remove (next n) e)"
    | "type_remove n Unit = Unit"
    | "type_remove n (Prod e1 e2) = Prod (type_remove n e1) (type_remove n e2)"
    | "type_remove n Void = Void"
    | "type_remove n (Sum e1 e2) = Sum (type_remove n e1) (type_remove n e2)"

primrec type_subst' :: "var => type => type => type"
where "type_subst' n e' (Tyvar v) = (if v = n then e' else Tyvar v)"
    | "type_subst' n e' Nat = Nat"
    | "type_subst' n e' (Arrow e1 e2) = Arrow (type_subst' n e' e1) (type_subst' n e' e2)"
    | "type_subst' n e' (All e) = All (type_subst' (next n) (type_insert first e') e)"
    | "type_subst' n e' Unit = Unit"
    | "type_subst' n e' (Prod e1 e2) = Prod (type_subst' n e' e1) (type_subst' n e' e2)"
    | "type_subst' n e' Void = Void"
    | "type_subst' n e' (Sum e1 e2) = Sum (type_subst' n e' e1) (type_subst' n e' e2)"

definition type_subst :: "var => type => type => type"
where "type_subst n t' t = type_remove n (type_subst' n (type_insert n t') t)"

lemma [simp]: "type_remove n (type_insert n e) = e"
by (induction e arbitrary: n, simp_all)

lemma [simp]: "canswap m n ==> 
        type_insert m (type_insert n e) = type_insert (next n) (type_insert m e)"
by (induction e arbitrary: n m, simp_all)

datatype expr = 
  Var var
| Zero
| Suc expr
| Iter expr expr expr
| Lam type expr
| Appl expr expr
| TyLam expr
| TyAppl type expr
| Triv
| Pair expr expr
| ProjL expr
| ProjR expr
| Abort type expr
| Case expr expr expr
| InL type type expr
| InR type type expr

primrec insert :: "var => expr => expr"
where "insert n (Var v) = Var (incr n v)"
    | "insert n Zero = Zero"
    | "insert n (Suc e) = Suc (insert n e)"
    | "insert n (Iter et e0 es) = Iter (insert n et) (insert n e0) (insert (next n) es)"
    | "insert n (Lam t e) = Lam t (insert (next n) e)"
    | "insert n (Appl e1 e2) = Appl (insert n e1) (insert n e2)"
    | "insert n (TyLam e) = TyLam (insert n e)"
    | "insert n (TyAppl t e) = TyAppl t (insert n e)"
    | "insert n Triv = Triv"
    | "insert n (Pair e1 e2) = Pair (insert n e1) (insert n e2)"
    | "insert n (ProjL e) = ProjL (insert n e)"
    | "insert n (ProjR e) = ProjR (insert n e)"
    | "insert n (Abort t e) = Abort t (insert n e)"
    | "insert n (Case et el er) = Case (insert n et) (insert (next n) el) (insert (next n) er)"
    | "insert n (InL t1 t2 e) = InL t1 t2 (insert n e)"
    | "insert n (InR t1 t2 e) = InR t1 t2 (insert n e)"

primrec remove :: "var => expr => expr"
where "remove n (Var v) = Var (subr n v)"
    | "remove n Zero = Zero"
    | "remove n (Suc e) = Suc (remove n e)"
    | "remove n (Iter et e0 es) = Iter (remove n et) (remove n e0) (remove (next n) es)"
    | "remove n (Lam t e) = Lam t (remove (next n) e)"
    | "remove n (Appl e1 e2) = Appl (remove n e1) (remove n e2)"
    | "remove n (TyLam e) = TyLam (remove n e)"
    | "remove n (TyAppl t e) = TyAppl t (remove n e)"
    | "remove n Triv = Triv"
    | "remove n (Pair e1 e2) = Pair (remove n e1) (remove n e2)"
    | "remove n (ProjL e) = ProjL (remove n e)"
    | "remove n (ProjR e) = ProjR (remove n e)"
    | "remove n (Abort t e) = Abort t (remove n e)"
    | "remove n (Case et el er) = Case (remove n et) (remove (next n) el) (remove (next n) er)"
    | "remove n (InL t1 t2 e) = InL t1 t2 (remove n e)"
    | "remove n (InR t1 t2 e) = InR t1 t2 (remove n e)"

primrec subst' :: "var => expr => expr => expr"
where "subst' n e' (Var v) = (if v = n then e' else Var v)"
    | "subst' n e' Zero = Zero"
    | "subst' n e' (Suc e) = Suc (subst' n e' e)"
    | "subst' n e' (Iter et e0 es) = 
                      Iter (subst' n e' et) 
                           (subst' n e' e0) 
                           (subst' (next n) (insert first e') es)"
    | "subst' n e' (Lam t e) = Lam t (subst' (next n) (insert first e') e)"
    | "subst' n e' (Appl e1 e2) = Appl (subst' n e' e1) (subst' n e' e2)"
    | "subst' n e' (TyLam e) = TyLam (subst' n e' e)"
    | "subst' n e' (TyAppl t e) = TyAppl t (subst' n e' e)"
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

definition subst :: "expr => expr => expr"
where "subst e' e = remove first (subst' first (insert first e') e)"

lemma [simp]: "remove n (insert n e) = e"
by (induction e arbitrary: n, simp_all)

lemma [simp]: "canswap m n ==> insert m (insert n e) = insert (next n) (insert m e)"
by (induction e arbitrary: n m, simp_all)

primrec subst_type :: "var => type => expr => expr"
where "subst_type n t' (Var v) = Var v"
    | "subst_type n t' Zero = Zero"
    | "subst_type n t' (Suc e) = Suc (subst_type n t' e)"
    | "subst_type n t' (Iter et e0 es) = 
                      Iter (subst_type n t' et) 
                           (subst_type n t' e0) 
                           (subst_type n t' es)"
    | "subst_type n t' (Lam t e) = Lam (type_subst n t' t) (subst_type n t' e)"
    | "subst_type n t' (Appl e1 e2) = Appl (subst_type n t' e1) (subst_type n t' e2)"
    | "subst_type n t' (TyLam e) = TyLam (subst_type (next n) (type_insert first t') e)"
    | "subst_type n t' (TyAppl t e) = TyAppl (type_subst n t' t) (subst_type n t' e)"
    | "subst_type n t' Triv = Triv"
    | "subst_type n t' (Pair e1 e2) = Pair (subst_type n t' e1) (subst_type n t' e2)"
    | "subst_type n t' (ProjL e) = ProjL (subst_type n t' e)"
    | "subst_type n t' (ProjR e) = ProjR (subst_type n t' e)"
    | "subst_type n t' (Abort t e) = Abort (type_subst n t' t) (subst_type n t' e)"
    | "subst_type n t' (Case et el er) = 
                      Case (subst_type n t' et) (subst_type n t' el) (subst_type n t' er)"
    | "subst_type n t' (InL t1 t2 e) = 
                      InL (type_subst n t' t1) (type_subst n t' t2) (subst_type n t' e)"
    | "subst_type n t' (InR t1 t2 e) = 
                      InR (type_subst n t' t1) (type_subst n t' t2) (subst_type n t' e)"

end
