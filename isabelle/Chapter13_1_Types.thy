theory Chapter13_1_Types
imports DeBruijnEnvironment
begin

datatype type = 
  TyVar var
| Nat
| Arrow type type
| Unit
| Prod type type
| Void
| Sum type type

primrec is_valid :: "unit env => type => bool"
where "is_valid del (TyVar v) = v in del"
    | "is_valid del Nat = True"
    | "is_valid del (Arrow t1 t2) = (is_valid del t1 & is_valid del t2)"
    | "is_valid del Unit = True"
    | "is_valid del (Prod t1 t2) = (is_valid del t1 & is_valid del t2)"
    | "is_valid del Void = True"
    | "is_valid del (Sum t1 t2) = (is_valid del t1 & is_valid del t2)"

primrec is_positive :: "var => type => bool"
where "is_positive t (TyVar v) = (v = t)"
    | "is_positive t Nat = True"
    | "is_positive t (Arrow t1 t2) = (is_valid empty_env t1 & is_positive t t2)"
    | "is_positive t Unit = True"
    | "is_positive t (Prod t1 t2) = (is_positive t t1 & is_positive t t2)"
    | "is_positive t Void = True"
    | "is_positive t (Sum t1 t2) = (is_positive t t1 & is_positive t t2)"

primrec type_insert :: "var => type => type"
where "type_insert n (TyVar v) = TyVar (incr n v)"
    | "type_insert n Nat = Nat"
    | "type_insert n (Arrow e1 e2) = Arrow (type_insert n e1) (type_insert n e2)"
    | "type_insert n Unit = Unit"
    | "type_insert n (Prod e1 e2) = Prod (type_insert n e1) (type_insert n e2)"
    | "type_insert n Void = Void"
    | "type_insert n (Sum e1 e2) = Sum (type_insert n e1) (type_insert n e2)"

primrec type_remove :: "var => type => type"
where "type_remove n (TyVar v) = TyVar (subr n v)"
    | "type_remove n Nat = Nat"
    | "type_remove n (Arrow e1 e2) = Arrow (type_remove n e1) (type_remove n e2)"
    | "type_remove n Unit = Unit"
    | "type_remove n (Prod e1 e2) = Prod (type_remove n e1) (type_remove n e2)"
    | "type_remove n Void = Void"
    | "type_remove n (Sum e1 e2) = Sum (type_remove n e1) (type_remove n e2)"

primrec type_subst' :: "var => type => type => type"
where "type_subst' n e' (TyVar v) = (if v = n then e' else TyVar v)"
    | "type_subst' n e' Nat = Nat"
    | "type_subst' n e' (Arrow e1 e2) = Arrow (type_subst' n e' e1) (type_subst' n e' e2)"
    | "type_subst' n e' Unit = Unit"
    | "type_subst' n e' (Prod e1 e2) = Prod (type_subst' n e' e1) (type_subst' n e' e2)"
    | "type_subst' n e' Void = Void"
    | "type_subst' n e' (Sum e1 e2) = Sum (type_subst' n e' e1) (type_subst' n e' e2)"

definition type_subst :: "type => type => type"
where "type_subst e' e = type_remove first (type_subst' first (type_insert first e') e)"

lemma [simp]: "type_remove n (type_insert n e) = e"
by (induction e arbitrary: n, simp_all)

lemma [simp]: "canswap m n ==> type_insert m (type_insert n e) = type_insert (next n) (type_insert m e)"
by (induction e arbitrary: n m, simp_all)

end
