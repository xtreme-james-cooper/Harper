theory Chapter16_1_Type
imports DeBruijnEnvironment
begin

datatype type = 
  Tyvar var
| Nat
| Arrow type type
| Unit
| Prod type type
| Void
| Sum type type
| Rec type

primrec type_insert :: "var => type => type"
where "type_insert n (Tyvar v) = Tyvar (incr n v)"
    | "type_insert n Nat = Nat"
    | "type_insert n (Arrow t1 t2) = Arrow (type_insert n t1) (type_insert n t2)"
    | "type_insert n Unit = Unit"
    | "type_insert n (Prod t1 t2) = Prod (type_insert n t1) (type_insert n t2)"
    | "type_insert n Void = Void"
    | "type_insert n (Sum t1 t2) = Sum (type_insert n t1) (type_insert n t2)"
    | "type_insert n (Rec t) = Rec (type_insert (next n) t)"

primrec type_remove :: "var => type => type"
where "type_remove n (Tyvar v) = Tyvar (subr n v)"
    | "type_remove n Nat = Nat"
    | "type_remove n (Arrow t1 t2) = Arrow (type_remove n t1) (type_remove n t2)"
    | "type_remove n Unit = Unit"
    | "type_remove n (Prod t1 t2) = Prod (type_remove n t1) (type_remove n t2)"
    | "type_remove n Void = Void"
    | "type_remove n (Sum t1 t2) = Sum (type_remove n t1) (type_remove n t2)"
    | "type_remove n (Rec t) = Rec (type_remove (next n) t)"

primrec type_subst' :: "var => type => type => type"
where "type_subst' n e' (Tyvar v) = (if v = n then e' else Tyvar v)"
    | "type_subst' n e' Nat = Nat"
    | "type_subst' n e' (Arrow t1 t2) = Arrow (type_subst' n e' t1) (type_subst' n e' t2)"
    | "type_subst' n e' Unit = Unit"
    | "type_subst' n e' (Prod t1 t2) = Prod (type_subst' n e' t1) (type_subst' n e' t2)"
    | "type_subst' n e' Void = Void"
    | "type_subst' n e' (Sum t1 t2) = Sum (type_subst' n e' t1) (type_subst' n e' t2)"
    | "type_subst' n e' (Rec t) = Rec (type_subst' (next n) (type_insert first e') t)"

definition type_subst :: "type => type => type"
where "type_subst e' e = type_remove first (type_subst' first (type_insert first e') e)"

lemma [simp]: "type_remove n (type_insert n e) = e"
by (induction e arbitrary: n, simp_all)

lemma [simp]: "canswap m n ==> 
          type_insert m (type_insert n e) = type_insert (next n) (type_insert m e)"
by (induction e arbitrary: n m, simp_all)

end
