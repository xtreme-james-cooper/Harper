theory Chapter16_1_Language
imports AssocList DeBruijn
begin

datatype type = 
  Arr type type 
| Unit 
| Prod type type 
| Void 
| Sum type type
| Tyvar nat
| Rec type

primrec is_valid_type :: "nat set => type => bool"
where "is_valid_type tyvars (Arr t1 t2) = (is_valid_type tyvars t1 & is_valid_type tyvars t2)"
    | "is_valid_type tyvars Unit = True"
    | "is_valid_type tyvars (Prod t1 t2) = (is_valid_type tyvars t1 & is_valid_type tyvars t2)"
    | "is_valid_type tyvars Void = True"
    | "is_valid_type tyvars (Sum t1 t2) = (is_valid_type tyvars t1 & is_valid_type tyvars t2)"
    | "is_valid_type tyvars (Tyvar v) = (v : tyvars)"
    | "is_valid_type tyvars (Rec t) = is_valid_type (expand_set tyvars) t"

primrec free_type_vars :: "type => nat set"
where "free_type_vars (Tyvar v) = {v}"
    | "free_type_vars (Arr e1 e2) = free_type_vars e1 Un free_type_vars e2"
    | "free_type_vars Unit = {}"
    | "free_type_vars (Prod e1 e2) = free_type_vars e1 Un free_type_vars e2"
    | "free_type_vars Void = {}"
    | "free_type_vars (Sum e1 e2) = free_type_vars e1 Un free_type_vars e2"
    | "free_type_vars (Rec t) = redr_set (free_type_vars t)"

primrec type_sub_from :: "nat => type => type"
where "type_sub_from n (Tyvar v) = Tyvar (subr n v)"
    | "type_sub_from n (Arr e1 e2) = Arr (type_sub_from n e1) (type_sub_from n e2)"
    | "type_sub_from n Unit = Unit"
    | "type_sub_from n (Prod e1 e2) = Prod (type_sub_from n e1) (type_sub_from n e2)"
    | "type_sub_from n Void = Void"
    | "type_sub_from n (Sum e1 e2) = Sum (type_sub_from n e1) (type_sub_from n e2)"
    | "type_sub_from n (Rec t) = Rec (type_sub_from (Suc n) t)"

primrec type_incr_from :: "nat => type => type"
where "type_incr_from n (Tyvar v) = Tyvar (incr n v)"
    | "type_incr_from n (Arr e1 e2) = Arr (type_incr_from n e1) (type_incr_from n e2)"
    | "type_incr_from n Unit = Unit"
    | "type_incr_from n (Prod e1 e2) = Prod (type_incr_from n e1) (type_incr_from n e2)"
    | "type_incr_from n Void = Void"
    | "type_incr_from n (Sum e1 e2) = Sum (type_incr_from n e1) (type_incr_from n e2)"
    | "type_incr_from n (Rec t) = Rec (type_incr_from (Suc n) t)"

primrec type_subst :: "type => type => nat => type"
where "type_subst (Tyvar v) t x = (if v = x then t else Tyvar v)"
    | "type_subst (Arr t1 t2) t x = Arr (type_subst t1 t x) (type_subst t2 t x)"
    | "type_subst Unit t x = Unit"
    | "type_subst (Prod t1 t2) t x = Prod (type_subst t1 t x) (type_subst t2 t x)"
    | "type_subst Void t x = Void"
    | "type_subst (Sum t1 t2) t x = Sum (type_subst t1 t x) (type_subst t2 t x)"
    | "type_subst (Rec t0) t x = Rec (type_subst t0 (type_incr_from 0 t) (Suc x))"

definition safe_type_subst :: "type => type => type"
where "safe_type_subst e e' = type_sub_from 0 (type_subst e (type_incr_from 0 e') 0)"

lemma [simp]: "free_type_vars (type_incr_from n e) = incr n ` free_type_vars e"
by (induction e arbitrary: n, auto)

lemma valid_incr_type: "is_valid_type (expand_set_at m s) (type_incr_from m t) = is_valid_type s t"
by (induction t arbitrary: s m, simp_all)

lemma [simp]: "is_valid_type (expand_set s) (type_incr_from 0 t) = is_valid_type s t"
proof -
  from valid_incr_type have X: "is_valid_type (expand_set_at 0 s) (type_incr_from 0 t) = is_valid_type s t" by presburger
  have "expand_set_at 0 s = expand_set s" by simp
  with X show "is_valid_type (expand_set s) (type_incr_from 0 t) = is_valid_type s t" by simp
qed

lemma [simp]: "m < n ==> type_incr_from m (type_sub_from n t) = type_sub_from (Suc n) (type_incr_from m t)"
by (induction t arbitrary: n m, simp_all)

lemma [simp]: "m <= n ==> type_incr_from m (type_incr_from n t) = type_incr_from (Suc n) (type_incr_from m t)"
by (induction t arbitrary: n m, simp_all)

lemma [simp]: "type_incr_from m (type_subst a t x) = type_subst (type_incr_from m a) (type_incr_from m t) (incr m x)"
by (induction a arbitrary: t x m, auto simp add: incr_def)

primrec type_incr_by :: "nat => type => type"
where "type_incr_by 0 e = e"
    | "type_incr_by (Suc n) e = type_incr_from 0 (type_incr_by n e)"

lemma [simp]:  "redr_set_by n (free_type_vars (type_incr_by n e)) = free_type_vars e" 
by (induction n, simp_all) 

lemma [simp]: "free_type_vars (type_subst e e' x) = (if x : free_type_vars e then free_type_vars e - {x} Un free_type_vars e' else free_type_vars e)"
by (induction e arbitrary: e' x, auto)

datatype expr = 
  Var nat 
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
| Fold type expr
| Unfold expr

primrec free_vars :: "expr => nat set"
where "free_vars (Var v) = {v}"
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
    | "free_vars (Fold t e) = free_vars e"
    | "free_vars (Unfold e) = free_vars e"

primrec incr_from :: "nat => expr => expr"
where "incr_from n (Var v) = Var (incr n v)"
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
    | "incr_from n (Fold t e) = Fold t (incr_from n e)"
    | "incr_from n (Unfold e) = Unfold (incr_from n e)"

primrec sub_from :: "nat => expr => expr"
where "sub_from n (Var v) = Var (if v < n then v else v - 1)"
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
    | "sub_from n (Fold t e) = Fold t (sub_from n e)"
    | "sub_from n (Unfold e) = Unfold (sub_from n e)"

primrec subst :: "expr => expr => nat => expr"
where "subst (Var v) e x = (if v = x then e else Var v)"
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
    | "subst (Fold t n) e x = Fold t (subst n e x)"
    | "subst (Unfold n) e x = Unfold (subst n e x)"

definition safe_subst :: "expr => expr => expr"
where "safe_subst e e' = sub_from 0 (subst e (incr_from 0 e') 0)"

lemma [simp]: "free_vars (incr_from n e) = incr n ` free_vars e"
by (induction e arbitrary: n, auto)

primrec incr_by :: "nat => expr => expr"
where "incr_by 0 e = e"
    | "incr_by (Suc n) e = incr_from 0 (incr_by n e)"

lemma [simp]:  "redr_set_by n (free_vars (incr_by n e)) = free_vars e" 
by (induction n, simp_all) 

lemma [simp]: "free_vars (subst e e' x) = (if x : free_vars e then free_vars e - {x} Un free_vars e' else free_vars e)"
by (induction e arbitrary: e' x, auto)

lemma [simp]: "m <= n ==> incr_from (Suc n) (incr_from m e) = incr_from m (incr_from n e)"
by (induction e arbitrary: m n, simp_all add: incr_def)

lemma [simp]: "m <= n ==> n ~: free_vars e ==> sub_from (Suc n) (incr_from m e) = incr_from m (sub_from n e)"
by (induction e arbitrary: n m, auto simp add: incr_def)

lemma [simp]: "m <= x ==> subst (incr_from m e) (incr_from m e') (Suc x) = incr_from m (subst e e' x)"
proof (induction e arbitrary: m e' x) 
case (Var v) 
  thus ?case by (simp add: incr_def)
next case (Lam t b) 
  hence "subst (incr_from (Suc m) b) (incr_from (Suc m) (incr_from 0 e')) (Suc (Suc x)) = incr_from (Suc m) (subst b (incr_from 0 e') (Suc x))" by blast 
  thus ?case by simp
next case (Ap e1 e2) 
  thus ?case by simp
next case (Fix t b) 
  hence "subst (incr_from (Suc m) b) (incr_from (Suc m) (incr_from 0 e')) (Suc (Suc x)) = incr_from (Suc m) (subst b (incr_from 0 e') (Suc x))" by blast
  thus ?case by simp
next case Triv 
  thus ?case by simp
next case (Pair e1 e2) 
  thus ?case by simp
next case (ProjL e) 
  thus ?case by simp
next case (ProjR e) 
  thus ?case by simp
next case (Abort t e) 
  thus ?case by simp
next case (InL t t' e) 
  thus ?case by simp
next case (InR t t' e) 
  thus ?case by simp
next case (Case e el er) 
  from Case have "subst (incr_from m e) (incr_from m e') (Suc x) = incr_from m (subst e e' x)" by blast
  moreover from Case have "subst (incr_from (Suc m) el) (incr_from (Suc m) (incr_from 0 e')) (Suc (Suc x)) = incr_from (Suc m) (subst el (incr_from 0 e') (Suc x))" by blast
  moreover from Case have "subst (incr_from (Suc m) er) (incr_from (Suc m) (incr_from 0 e')) (Suc (Suc x)) = incr_from (Suc m) (subst er (incr_from 0 e') (Suc x))" by (metis Suc_le_mono)
  ultimately show ?case by simp
next case (Fold t e) 
  thus ?case by simp
next case (Unfold e)
  thus ?case by simp
qed 

lemma [simp]: "sub_from n (subst (incr_from n e) e' n) = e" 
by (induction e arbitrary: n e', simp_all add: incr_def)

lemma [simp]: "safe_subst (incr_from 0 e) e' = e"
by (simp add: safe_subst_def) 

end
