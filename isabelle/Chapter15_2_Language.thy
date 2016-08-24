theory Chapter15_2_Language
imports Chapter15_1_Types
begin

datatype expr = 
  Var var
| Zero
| Suc expr
| Iter expr expr expr
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
| Strgen type expr expr expr
| Hd expr
| Tl expr
| Fold type expr
| Rec type expr expr
| Unfold type expr
| Gen type expr expr

primrec insert :: "var \<Rightarrow> expr \<Rightarrow> expr" where 
  "insert n (Var v) = Var (incr n v)"
| "insert n Zero = Zero"
| "insert n (Suc e) = Suc (insert n e)"
| "insert n (Iter et e0 es) = Iter (insert n et) (insert n e0) (insert (next n) es)"
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
| "insert n (Strgen t e e1 e2) = Strgen t (insert n e) (insert (next n) e1) (insert (next n) e2)"
| "insert n (Hd e) = Hd (insert n e)"
| "insert n (Tl e) = Tl (insert n e)"
| "insert n (Fold t e) = Fold t (insert n e)"
| "insert n (Rec t e e1) = Rec t (insert n e) (insert (next n) e1)"
| "insert n (Fold t e) = Fold t (insert n e)"
| "insert n (Fold t e) = Fold t (insert n e)"

primrec subst :: "expr \<Rightarrow> var \<Rightarrow> expr \<Rightarrow> expr" where 
  "subst e' n (Var v) = (if v = n then e' else Var (subr n v))"
| "subst e' n Zero = Zero"
| "subst e' n (Suc e) = Suc (subst e' n e)"
| "subst e' n (Iter et e0 es) = 
    Iter (subst e' n et) (subst e' n e0) (subst (insert first e') (next n) es)"
| "subst e' n (Lam t e) = Lam t (subst (insert first e') (next n) e)"
| "subst e' n (Appl e1 e2) = Appl (subst e' n e1) (subst e' n e2)"
| "subst e' n Triv = Triv"
| "subst e' n (Pair e1 e2) = Pair (subst e' n e1) (subst e' n e2)"
| "subst e' n (ProjL e) = ProjL (subst e' n e)"
| "subst e' n (ProjR e) = ProjR (subst e' n e)"
| "subst e' n (Abort t e) = Abort t (subst e' n e)"
| "subst e' n (Case et el er) = 
    Case (subst e' n et) (subst (insert first e') (next n) el) 
      (subst (insert first e') (next n) er)"
| "subst e' n (InL t1 t2 e) = InL t1 t2 (subst e' n e)"
| "subst e' n (InR t1 t2 e) = InR t1 t2 (subst e' n e)"
| "subst e' n (Strgen t e e1 e2) = Strgen t (subst e' n e) (subst (insert first e') (next n) e1) 
      (subst (insert first e') (next n) e2)"
| "subst e' n (Hd e) = Hd (subst e' n e)"
| "subst e' n (Tl e) = Tl (subst e' n e)"

lemma [simp]: "canswap m n \<Longrightarrow> insert m (insert n e) = insert (next n) (insert m e)"
  by (induction e arbitrary: n m) simp_all

lemma [simp]: "subst e' n (insert n e) = e"
  by (induction e arbitrary: n e') simp_all

end
