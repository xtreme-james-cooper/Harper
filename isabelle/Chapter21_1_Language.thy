theory Chapter21_1_Language
imports DeBruijnEnvironment
begin

datatype kind =
  Star

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

primrec type_subst :: "type => var => type => type"
where "type_subst e' n (Tyvar v) = (if v = n then e' else Tyvar (subr n v))"
    | "type_subst e' n Nat = Nat"
    | "type_subst e' n (Arrow e1 e2) = Arrow (type_subst e' n e1) (type_subst e' n e2)"
    | "type_subst e' n (All e) = All (type_subst (type_insert first e') (next n) e)"
    | "type_subst e' n Unit = Unit"
    | "type_subst e' n (Prod e1 e2) = Prod (type_subst e' n e1) (type_subst e' n e2)"
    | "type_subst e' n Void = Void"
    | "type_subst e' n (Sum e1 e2) = Sum (type_subst e' n e1) (type_subst e' n e2)"

lemma [simp]: "canswap m n ==> 
        type_insert m (type_insert n e) = type_insert (next n) (type_insert m e)"
by (induction e arbitrary: n m, simp_all)

lemma [simp]: "canswap m n ==> 
        type_insert m o type_insert n = type_insert (next n) o type_insert m"
by auto

lemma [simp]: "canswap m n ==> type_insert m (type_subst t' n t) =
                  type_subst (type_insert m t') (next n) (type_insert m t)"
by (induction t arbitrary: m n t', simp_all)

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

primrec expr_insert_type :: "var => expr => expr"
where "expr_insert_type n (Var v) = Var v"
    | "expr_insert_type n Zero = Zero"
    | "expr_insert_type n (Suc e) = Suc (expr_insert_type n e)"
    | "expr_insert_type n (Iter et e0 es) = 
                      Iter (expr_insert_type n et) 
                           (expr_insert_type n e0) 
                           (expr_insert_type n es)"
    | "expr_insert_type n (Lam t e) = Lam (type_insert n t) (expr_insert_type n e)"
    | "expr_insert_type n (Appl e1 e2) = Appl (expr_insert_type n e1) (expr_insert_type n e2)"
    | "expr_insert_type n (TyLam e) = TyLam (expr_insert_type (next n) e)"
    | "expr_insert_type n (TyAppl t e) = TyAppl (type_insert n t) (expr_insert_type n e)"
    | "expr_insert_type n Triv = Triv"
    | "expr_insert_type n (Pair e1 e2) = Pair (expr_insert_type n e1) (expr_insert_type n e2)"
    | "expr_insert_type n (ProjL e) = ProjL (expr_insert_type n e)"
    | "expr_insert_type n (ProjR e) = ProjR (expr_insert_type n e)"
    | "expr_insert_type n (Abort t e) = Abort (type_insert n t) (expr_insert_type n e)"
    | "expr_insert_type n (Case et el er) = 
                      Case (expr_insert_type n et) (expr_insert_type n el) (expr_insert_type n er)"
    | "expr_insert_type n (InL t1 t2 e) = 
                      InL (type_insert n t1) (type_insert n t2) (expr_insert_type n e)"
    | "expr_insert_type n (InR t1 t2 e) = 
                      InR (type_insert n t1) (type_insert n t2) (expr_insert_type n e)"

primrec subst :: "expr => var => expr => expr"
where "subst e' n (Var v) = (if v = n then e' else Var (subr n v))"
    | "subst e' n Zero = Zero"
    | "subst e' n (Suc e) = Suc (subst e' n e)"
    | "subst e' n (Iter et e0 es) = 
                      Iter (subst e' n et) 
                           (subst e' n e0) 
                           (subst (insert first e') (next n) es)"
    | "subst e' n (Lam t e) = Lam t (subst (insert first e') (next n) e)"
    | "subst e' n (Appl e1 e2) = Appl (subst e' n e1) (subst e' n e2)"
    | "subst e' n (TyLam e) = TyLam (subst (expr_insert_type first e') n e)"
    | "subst e' n (TyAppl t e) = TyAppl t (subst e' n e)"
    | "subst e' n Triv = Triv"
    | "subst e' n (Pair e1 e2) = Pair (subst e' n e1) (subst e' n e2)"
    | "subst e' n (ProjL e) = ProjL (subst e' n e)"
    | "subst e' n (ProjR e) = ProjR (subst e' n e)"
    | "subst e' n (Abort t e) = Abort t (subst e' n e)"
    | "subst e' n (Case et el er) = 
                      Case (subst e' n et) 
                           (subst (insert first e') (next n)el) 
                           (subst (insert first e') (next n) er)"
    | "subst e' n (InL t1 t2 e) = InL t1 t2 (subst e' n e)"
    | "subst e' n (InR t1 t2 e) = InR t1 t2 (subst e' n e)"

primrec expr_subst_type :: "type => var => expr => expr"
where "expr_subst_type t' n (Var v) = Var v"
    | "expr_subst_type t' n Zero = Zero"
    | "expr_subst_type t' n (Suc e) = Suc (expr_subst_type t' n e)"
    | "expr_subst_type t' n (Iter et e0 es) = 
                      Iter (expr_subst_type t' n et) 
                           (expr_subst_type t' n e0) 
                           (expr_subst_type t' n es)"
    | "expr_subst_type t' n (Lam t e) = Lam (type_subst t' n t) (expr_subst_type t' n e)"
    | "expr_subst_type t' n (Appl e1 e2) = 
                Appl (expr_subst_type t' n e1) (expr_subst_type t' n e2)"
    | "expr_subst_type t' n (TyLam e) = TyLam (expr_subst_type (type_insert first t') (next n) e)"
    | "expr_subst_type t' n (TyAppl t e) = TyAppl (type_subst t' n t) (expr_subst_type t' n e)"
    | "expr_subst_type t' n Triv = Triv"
    | "expr_subst_type t' n (Pair e1 e2) = 
            Pair (expr_subst_type t' n e1) (expr_subst_type t' n e2)"
    | "expr_subst_type t' n (ProjL e) = ProjL (expr_subst_type t' n e)"
    | "expr_subst_type t' n (ProjR e) = ProjR (expr_subst_type t' n e)"
    | "expr_subst_type t' n (Abort t e) = Abort (type_subst t' n t) (expr_subst_type t' n e)"
    | "expr_subst_type t' n (Case et el er) = 
            Case (expr_subst_type t' n et) (expr_subst_type t' n el) (expr_subst_type t' n er)"
    | "expr_subst_type t' n (InL t1 t2 e) = 
                      InL (type_subst t' n t1) (type_subst t' n t2) (expr_subst_type t' n e)"
    | "expr_subst_type t' n (InR t1 t2 e) = 
                      InR (type_subst t' n t1) (type_subst t' n t2) (expr_subst_type t' n e)"

lemma [simp]: "canswap m n ==> insert m (insert n e) = insert (next n) (insert m e)"
by (induction e arbitrary: n m, simp_all)

lemma [simp]: "insert n (expr_insert_type m e) = expr_insert_type m (insert n e)"
by (induction e arbitrary: n m, simp_all)

lemma [simp]: "canswap n m ==> expr_insert_type n (expr_insert_type m e) = 
                    expr_insert_type (next m) (expr_insert_type n e)"
by (induction e arbitrary: n m, simp_all)

lemma [simp]: "canswap m n ==> 
        type_insert m (type_insert n e) = type_insert (next n) (type_insert m e)"
by (induction e arbitrary: n m, simp_all)

lemma [simp]: "canswap m n ==> type_insert m o type_insert n = type_insert (next n) o type_insert m"
by auto

lemma [simp]: "canswap m n ==> type_insert m (type_subst t' n t) =
                  type_subst (type_insert m t') (next n) (type_insert m t)"
by (induction t arbitrary: m n t', simp_all)

lemma [simp]: "canswap m n ==> type_insert m o type_subst t' n = 
                                   type_subst (type_insert m t') (next n) o type_insert m"
by auto

lemma [simp]: "type_subst t' n (type_insert n t) = t"
by (induction t arbitrary: n t', simp_all)

lemma [simp]: "canswap m n ==> type_subst (type_insert n t') m (type_insert (next n) t) = 
                                    type_insert n (type_subst t' m t)"
by (induction t arbitrary: n m t', simp_all)

lemma [simp]: "canswap m n ==> 
                  type_subst (type_subst t' n t'') m (type_subst (type_insert m t') (next n) t) = 
                      type_subst t' n (type_subst t'' m t)"
proof (induction t arbitrary: n m t' t'')
case (Tyvar v)
  thus ?case by (cases n, cases m, cases v, auto)
next case Arrow
  thus ?case by simp
next case All
  thus ?case by simp
next case Nat
  thus ?case by simp
next case Unit
  thus ?case by simp
next case Prod
  thus ?case by simp
next case Void
  thus ?case by simp
next case Sum
  thus ?case by simp
qed

end
