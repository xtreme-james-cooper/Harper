theory Chapter12_1_Language
imports DeBruijnEnvironment
begin

datatype type = 
  Nat
| Arrow type type
| Unit
| Prod type type
| Void
| Sum type type

datatype patn =
  WildPat
| VarPat
| TrivPat
| PairPat patn patn
| InLPat patn
| InRPat patn

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
| Abort type expr
| Case expr expr expr
| InL type type expr
| InR type type expr
| Match expr "rule list"
and rule = 
  Rule patn expr

fun pat_var_count :: "patn => nat"
where "pat_var_count WildPat = 0"
    | "pat_var_count VarPat = 1"
    | "pat_var_count TrivPat = 0"
    | "pat_var_count (PairPat p1 p2) = pat_var_count p1 + pat_var_count p2"
    | "pat_var_count (InLPat p) = pat_var_count p"
    | "pat_var_count (InRPat p) = pat_var_count p"

primrec insert :: "var => expr => expr"
    and insert_rules :: "var => rule list => rule list"
    and insert_rule :: "var => rule => rule"
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
    | "insert n (Abort t e) = Abort t (insert n e)"
    | "insert n (Case et el er) = Case (insert n et) (insert (next n) el) (insert (next n) er)"
    | "insert n (InL t1 t2 e) = InL t1 t2 (insert n e)"
    | "insert n (InR t1 t2 e) = InR t1 t2 (insert n e)"
    | "insert n (Match e rs) = Match (insert n e) (insert_rules n rs)"
    | "insert_rules n [] = []"
    | "insert_rules n (r # rs) = insert_rule n r # insert_rules n rs"
    | "insert_rule n (Rule p e) = Rule p (insert (next_by (pat_var_count p) n) e)"

primrec mult_insert :: "nat => expr => expr"
where "mult_insert 0 e = e"
    | "mult_insert (Nat.Suc n) e = insert first (mult_insert n e)"

primrec remove :: "var => expr => expr"
    and remove_rules :: "var => rule list => rule list"
    and remove_rule :: "var => rule => rule"
where "remove n (Var v) = Var (subr n v)"
    | "remove n Zero = Zero"
    | "remove n (Suc e) = Suc (remove n e)"
    | "remove n (Rec et e0 es) = Rec (remove n et) (remove n e0) (remove (next (next n)) es)"
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
    | "remove n (Match e rs) = Match (remove n e) (remove_rules n rs)"
    | "remove_rules n [] = []"
    | "remove_rules n (r # rs) = remove_rule n r # remove_rules n rs"
    | "remove_rule n (Rule p e) = Rule p (remove (next_by (pat_var_count p) n) e)"

primrec subst' :: "var => expr => expr => expr"
    and subst_rules :: "var => expr => rule list => rule list"
    and subst_rule :: "var => expr => rule => rule"
where "subst' n e' (Var v) = (if v = n then e' else Var v)"
    | "subst' n e' Zero = Zero"
    | "subst' n e' (Suc e) = Suc (subst' n e' e)"
    | "subst' n e' (Rec et e0 es) = 
                      Rec (subst' n e' et) 
                          (subst' n e' e0) 
                          (subst' (next (next n)) (insert first (insert first e')) es)"
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
    | "subst' n e' (Match e rs) = Match (subst' n e' e) (subst_rules n e' rs)"
    | "subst_rules n e' [] = []"
    | "subst_rules n e' (r # rs) = subst_rule n e' r # subst_rules n e' rs"
    | "subst_rule n e' (Rule p e) = Rule p (subst' (next_by (pat_var_count p) n) 
                                                   (mult_insert (pat_var_count p) e') e)"

definition subst :: "expr => var => expr => expr"
where "subst e' n e = remove first (subst' first (insert first e') e)"

lemma [simp]: "remove n (insert n e) = e"
  and [simp]: "remove_rules n (insert_rules n rs) = rs"
  and [simp]: "remove_rule n (insert_rule n r) = r"
by (induction e and rs and r arbitrary: n and n and n, simp_all)

lemma [simp]: "canswap m n ==> insert m (insert n e) = insert (next n) (insert m e)"
  and [simp]: "canswap m n ==> 
        insert_rules m (insert_rules n rs) = insert_rules (next n) (insert_rules m rs)"
  and [simp]: "canswap m n ==> 
        insert_rule m (insert_rule n r) = insert_rule (next n) (insert_rule m r)"
by (induction e and rs and r arbitrary: n m and n m and n m, simp_all)

lemma [simp]: "mult_insert m (insert n e) = insert (next_by m n) (mult_insert m e)"
by (induction m arbitrary: n e, simp_all)

end
