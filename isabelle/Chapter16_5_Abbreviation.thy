theory Chapter16_5_Abbreviation
imports Chapter16_4_Evaluation
begin

definition Nat :: type
where "Nat = Rec (Sum Unit (Tyvar first))"

definition Zero :: expr
where "Zero = Fold (Sum Unit (Tyvar first)) (InL Unit Nat Triv)"

definition Suc :: "expr => expr"
where "Suc e = Fold (Sum Unit (Tyvar first)) (InR Unit Nat e)"

definition IsZ :: "expr => expr => expr => expr"
where "IsZ et e0 es = Case (Unfold et) (insert first e0) es"

lemma [simp]: "typecheck gam Zero Nat" 
by (simp add: Zero_def Nat_def type_subst_def)
lemma [simp]: "typecheck gam e Nat ==> typecheck gam (Suc e) Nat" 
by (simp add: Suc_def Nat_def type_subst_def)
lemma [simp]: "typecheck gam et Nat ==> typecheck gam e0 t ==> 
                typecheck (extend gam Nat) es t ==> typecheck gam (IsZ et e0 es) t"
proof (simp add: IsZ_def Nat_def type_subst_def)
  assume A: "typecheck gam et (Rec (Sum Unit (Tyvar first)))"
     and B: "typecheck gam e0 t"
     and C: "typecheck (extend gam (Rec (Sum Unit (Tyvar first)))) es t"
  with tc_unfold type_subst_def have "typecheck gam et (Rec (Sum Unit (Tyvar first))) ==> 
                typecheck gam (Unfold et) (Sum Unit (Rec (Sum Unit (Tyvar first))))" by fastforce 
  with A Nat_def B C show "typecheck gam (Case (Unfold et) (insert first e0) es) t" by simp
qed

lemma [simp]: "eval e e' ==> eval (Suc e) (Suc e')"
by (simp add: Suc_def)
lemma [simp]: "eval et et' ==> eval (IsZ et e0 es) (IsZ et' e0 es)"
by (simp add: IsZ_def)
lemma [simp]: "EX e'. eval (IsZ Zero e0 es) e' & eval e' e0"
proof (simp add: IsZ_def Zero_def)
  have "eval (Case (InL Unit Nat Triv) (insert first e0) es) (subst Triv first (insert first e0))" 
  by (metis eval_case_2 is_val.simps(4))
  thus "EX e'. eval (Case (Unfold (Fold (Sum Unit (Tyvar first)) (InL Unit Nat Triv)))
                          (insert first e0) es) e' &
         eval e' e0 " by force
qed

lemma [simp]: "is_val et ==> EX e'. eval (IsZ (Suc et) e0 es) e' & eval e' (subst et first es)"
by (metis Suc_def IsZ_def eval_case_1 eval_case_3 eval_unfold_2 is_val.simps(11))

lemma canonical_nat_like: "typecheck env e t ==> is_val e ==> 
    (t = Nat --> e = Zero | (EX v. typecheck env v Nat & is_val v & e = Suc v)) & 
    (t = Sum Unit Nat --> e = InL Unit Nat Triv | 
              (EX v. typecheck env v Nat & is_val v & e = InR Unit Nat v))"
proof (induction env e t rule: typecheck.induct) 
case tc_var
  thus ?case by simp
next case tc_lam
  thus ?case by (simp add: Nat_def)
next case tc_appl
  thus ?case by simp
next case tc_triv
  thus ?case by (simp add: Nat_def)
next case tc_pair
  thus ?case by (simp add: Nat_def)
next case tc_projl
  thus ?case by simp
next case tc_projr
  thus ?case by simp
next case tc_abort
  thus ?case by simp
next case tc_case
  thus ?case by simp
next case (tc_inl gam e t1 t2)
  with canonical_unit have "t1 = Unit ==> e = Triv" by force
  thus ?case by (simp add: Nat_def canonical_unit)
next case (tc_inr gam e t1 t2)
  hence "t1 = Rec (Sum Unit (Tyvar first)) ==> 
            typecheck gam e (Rec (Sum Unit (Tyvar first)))" by fast
  with tc_inr show ?case by (simp add: Nat_def)
next case tc_fix
  thus ?case by simp
next case (tc_fold gam e t)
  thus ?case by (auto simp add: Nat_def Zero_def Suc_def type_subst_def)
next case tc_unfold
  thus ?case by simp
qed 

lemma canonical_nat: "is_val e ==> typecheck env e Nat ==> 
            e = Zero | (EX v. typecheck env v Nat & is_val v & e = Suc v)"
by (simp add: canonical_nat_like)

end
