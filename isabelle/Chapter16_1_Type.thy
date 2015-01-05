theory Chapter16_1_Type
imports DeBruijnEnvironment
begin

datatype type = 
  Tyvar var
| Arrow type type
| Unit
| Prod type type
| Void
| Sum type type
| Rec type

primrec type_insert :: "var => type => type"
where "type_insert n (Tyvar v) = Tyvar (incr n v)"
    | "type_insert n (Arrow t1 t2) = Arrow (type_insert n t1) (type_insert n t2)"
    | "type_insert n Unit = Unit"
    | "type_insert n (Prod t1 t2) = Prod (type_insert n t1) (type_insert n t2)"
    | "type_insert n Void = Void"
    | "type_insert n (Sum t1 t2) = Sum (type_insert n t1) (type_insert n t2)"
    | "type_insert n (Rec t) = Rec (type_insert (next n) t)"

primrec type_subst :: "type => var => type => type"
where "type_subst e' n (Tyvar v) = (if v = n then e' else Tyvar (subr n v))"
    | "type_subst e' n (Arrow t1 t2) = Arrow (type_subst e' n t1) (type_subst e' n t2)"
    | "type_subst e' n Unit = Unit"
    | "type_subst e' n (Prod t1 t2) = Prod (type_subst e' n t1) (type_subst e' n t2)"
    | "type_subst e' n Void = Void"
    | "type_subst e' n (Sum t1 t2) = Sum (type_subst e' n t1) (type_subst e' n t2)"
    | "type_subst e' n (Rec t) = Rec (type_subst (type_insert first e') (next n) t)"

lemma [simp]: "canswap m n ==> 
          type_insert m (type_insert n e) = type_insert (next n) (type_insert m e)"
by (induction e arbitrary: n m, simp_all)

end
