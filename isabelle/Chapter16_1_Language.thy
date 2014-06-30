theory Chapter16_1_Language
imports AssocList DeBruijn
begin

datatype type = 
  Nat 
| Arr type type 
| Unit 
| Prod type type 
| Void 
| Sum type type
| Tyvar string
| Rec string type

primrec is_valid_type :: "string set => type => bool"
where "is_valid_type tyvars Nat = True"
    | "is_valid_type tyvars (Arr t1 t2) = (is_valid_type tyvars t1 & is_valid_type tyvars t2)"
    | "is_valid_type tyvars Unit = True"
    | "is_valid_type tyvars (Prod t1 t2) = (is_valid_type tyvars t1 & is_valid_type tyvars t2)"
    | "is_valid_type tyvars Void = True"
    | "is_valid_type tyvars (Sum t1 t2) = (is_valid_type tyvars t1 & is_valid_type tyvars t2)"
    | "is_valid_type tyvars (Tyvar v) = (v : tyvars)"
    | "is_valid_type tyvars (Rec v t) = (is_valid_type (insert v tyvars) t)"

datatype expr = 
  Var nat 
| Zero
| Succ expr
| IsZ expr expr expr
| Lam type expr
| Ap expr expr
| Fix type expr
| Triv
| Pair expr expr
| ProjL expr
| ProjR expr
| Abort type expr
| InL type type expr
| InR type type expr
| Case expr expr expr
| Fold string type expr
| Unfold expr

primrec free_vars :: "expr => nat set"
where "free_vars (Var v) = {v}"
    | "free_vars Zero = {}"
    | "free_vars (Succ e) = free_vars e"
    | "free_vars (IsZ e0 e1 et) = free_vars e0 Un free_vars et Un redr_set (free_vars e1)"
    | "free_vars (Lam t b) = redr_set (free_vars b)"
    | "free_vars (Ap e1 e2) = free_vars e1 Un free_vars e2"
    | "free_vars (Fix t b) = redr_set (free_vars b)"
    | "free_vars Triv = {}"
    | "free_vars (Pair e1 e2) = free_vars e1 Un free_vars e2"
    | "free_vars (ProjL e) = free_vars e"
    | "free_vars (ProjR e) = free_vars e"
    | "free_vars (Abort t e) = free_vars e"
    | "free_vars (InL t t' e) = free_vars e"
    | "free_vars (InR t t' e) = free_vars e"
    | "free_vars (Case e el er) = free_vars e Un redr_set (free_vars el) Un redr_set (free_vars er)"
    | "free_vars (Fold v t e) = free_vars e"
    | "free_vars (Unfold e) = free_vars e"

primrec incr_from :: "nat => expr => expr"
where "incr_from n (Var v) = Var (incr n v)"
    | "incr_from n Zero = Zero"
    | "incr_from n (Succ e) = Succ (incr_from n e)"
    | "incr_from n (IsZ e0 e1 et) = IsZ (incr_from n e0) (incr_from (Suc n) e1) (incr_from n et)"
    | "incr_from n (Lam t b) = Lam t (incr_from (Suc n) b)"
    | "incr_from n (Ap e1 e2) = Ap (incr_from n e1) (incr_from n e2)"
    | "incr_from n (Fix t b) = Fix t (incr_from (Suc n) b)"
    | "incr_from n Triv = Triv"
    | "incr_from n (Pair e1 e2) = Pair (incr_from n e1) (incr_from n e2)"
    | "incr_from n (ProjL e) = ProjL (incr_from n e)"
    | "incr_from n (ProjR e) = ProjR (incr_from n e)"
    | "incr_from n (Abort t e) = Abort t (incr_from n e)"
    | "incr_from n (InL t t' e) = InL t t' (incr_from n e)"
    | "incr_from n (InR t t' e) = InR t t' (incr_from n e)"
    | "incr_from n (Case e el er) = Case (incr_from n e) (incr_from (Suc n) el) (incr_from (Suc n) er)"
    | "incr_from n (Fold v t e) = Fold v t (incr_from n e)"
    | "incr_from n (Unfold e) = Unfold (incr_from n e)"

lemma [simp]: "free_vars (incr_from n e) = incr n ` free_vars e"
by (induction e arbitrary: n, auto)

primrec incr_by :: "nat => expr => expr"
where "incr_by 0 e = e"
    | "incr_by (Suc n) e = incr_from 0 (incr_by n e)"

lemma [simp]:  "redr_set_by n (free_vars (incr_by n e)) = free_vars e" 
by (induction n, simp_all) 

primrec sub_from :: "nat => expr => expr"
where "sub_from n (Var v) = Var (if v < n then v else if v = n then undefined else v - 1)"
    | "sub_from n Zero = Zero"
    | "sub_from n (Succ e) = Succ (sub_from n e)"
    | "sub_from n (IsZ e0 e1 et) = IsZ (sub_from n e0) (sub_from (Suc n) e1) (sub_from n et)"
    | "sub_from n (Lam t b) = Lam t (sub_from (Suc n) b)"
    | "sub_from n (Ap e1 e2) = Ap (sub_from n e1) (sub_from n e2)"
    | "sub_from n (Fix t b) = Fix t (sub_from (Suc n) b)"
    | "sub_from n Triv = Triv"
    | "sub_from n (Pair e1 e2) = Pair (sub_from n e1) (sub_from n e2)"
    | "sub_from n (ProjL e) = ProjL (sub_from n e)"
    | "sub_from n (ProjR e) = ProjR (sub_from n e)"
    | "sub_from n (Abort t e) = Abort t (sub_from n e)"
    | "sub_from n (InL t t' e) = InL t t' (sub_from n e)"
    | "sub_from n (InR t t' e) = InR t t' (sub_from n e)"
    | "sub_from n (Case e el er) = Case (sub_from n e) (sub_from (Suc n) el) (sub_from (Suc n) er)"

primrec subst :: "expr => expr => nat => expr"
where "subst (Var v) e x = (if v = x then e else Var v)"
    | "subst Zero e x = Zero"
    | "subst (Succ n) e x = Succ (subst n e x)"
    | "subst (IsZ e0 e1 et) e x = IsZ (subst e0 e x) (subst e1 (incr_from 0 e) (Suc x)) (subst et e x)"
    | "subst (Lam t b) e x = Lam t (subst b (incr_from 0 e) (Suc x))"
    | "subst (Ap e1 e2) e x = Ap (subst e1 e x) (subst e2 e x)"
    | "subst (Fix t b) e x = Fix t (subst b (incr_from 0 e) (Suc x))"
    | "subst Triv e x = Triv"
    | "subst (Pair e1 e2) e x = Pair (subst e1 e x) (subst e2 e x)"
    | "subst (ProjL n) e x = ProjL (subst n e x)"
    | "subst (ProjR n) e x = ProjR (subst n e x)"
    | "subst (Abort t n) e x = Abort t (subst n e x)"
    | "subst (InL t t' n) e x = InL t t' (subst n e x)"
    | "subst (InR t t' n) e x = InR t t' (subst n e x)"
    | "subst (Case n el er) e x = Case (subst n e x) (subst el (incr_from 0 e) (Suc x)) (subst er (incr_from 0 e) (Suc x))"

definition safe_subst :: "expr => expr => expr"
where "safe_subst e e' = sub_from 0 (subst e (incr_from 0 e') 0)"

lemma [simp]: "free_vars (subst e e' x) = (if x : free_vars e then free_vars e - {x} Un free_vars e' else free_vars e)"
by (induction e arbitrary: e' x, auto)

end
