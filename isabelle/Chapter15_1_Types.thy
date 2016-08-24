theory Chapter15_1_Types
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
| Stream
| Ind type
| Coind type

primrec type_insert :: "var \<Rightarrow> type \<Rightarrow> type" where
  "type_insert n (TyVar v) = TyVar (incr n v)"
| "type_insert n Nat = Nat"
| "type_insert n (Arrow t1 t2) = Arrow (type_insert n t1) (type_insert n t2)"
| "type_insert n Unit = Unit"
| "type_insert n (Prod t1 t2) = Prod (type_insert n t1) (type_insert n t2)"
| "type_insert n Void = Void"
| "type_insert n (Sum t1 t2) = Sum (type_insert n t1) (type_insert n t2)"
| "type_insert n Stream = Stream"
| "type_insert n (Ind t) = Ind (type_insert (next n) t)"
| "type_insert n (Coind t) = Coind (type_insert (next n) t)"

primrec type_subst :: "type \<Rightarrow> var \<Rightarrow> type \<Rightarrow> type" where
  "type_subst t' n (TyVar v) = (if n = v then t' else TyVar (subr n v))" 
| "type_subst t' n Nat = Nat"
| "type_subst t' n (Arrow t1 t2) = Arrow (type_subst t' n  t1) (type_subst t' n  t2)"
| "type_subst t' n Unit = Unit"
| "type_subst t' n (Prod t1 t2) = Prod (type_subst t' n  t1) (type_subst t' n  t2)"
| "type_subst t' n Void = Void"
| "type_subst t' n (Sum t1 t2) = Sum (type_subst t' n  t1) (type_subst t' n  t2)"
| "type_subst t' n Stream = Stream"
| "type_subst t' n (Ind t) = Ind (type_subst (type_insert first t') (next n) t)"
| "type_subst t' n (Coind t) = Coind (type_subst (type_insert first t') (next n) t)"

primrec valid_type :: "unit env \<Rightarrow> type \<Rightarrow> bool" where
  "valid_type del (TyVar v) = (v in del)" 
| "valid_type del Nat = True"
| "valid_type del (Arrow t1 t2) = (valid_type del t1 \<and> valid_type del t2)"
| "valid_type del Unit = True"
| "valid_type del (Prod t1 t2) = (valid_type del t1 \<and> valid_type del t2)"
| "valid_type del Void = True"
| "valid_type del (Sum t1 t2) = (valid_type del t1 \<and> valid_type del t2)"
| "valid_type del Stream = True"
| "valid_type del (Ind t) = valid_type (extend del ()) t"
| "valid_type del (Coind t) = valid_type (extend del ()) t"

end
