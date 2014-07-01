theory Chapter20_4_Abbreviations
imports Chapter20_3_Evaluation
begin

abbreviation Nat :: type
where "Nat == Rec (Sum Unit (Tyvar 0))"

lemma "is_valid_type {} Nat" by simp
lemma "free_type_vars Nat = {}" by simp
lemma "type_sub_from n Nat = Nat" by simp
lemma "type_incr_from n Nat = Nat" by simp
lemma "type_subst Nat t x = Nat" by simp

abbreviation Zero :: expr
where "Zero == Fold (Sum Unit (Tyvar 0)) (InL Unit Nat Triv)"

lemma "free_vars Zero = {}" by simp
lemma "incr_from n Zero = Zero" by simp
lemma "sub_from n Zero = Zero" by simp
lemma "subst Zero e x = Zero" by simp
lemma "typecheck env Zero Nat" by (simp add: safe_type_subst_def)
lemma "is_val Zero" by simp

abbreviation Succ :: "expr => expr"
where "Succ e == Fold (Sum Unit (Tyvar 0)) (InR Unit Nat e)"

lemma "free_vars (Succ e) = free_vars e" by simp
lemma "incr_from n (Succ e) = Succ (incr_from n e)" by simp
lemma "sub_from n (Succ e) = Succ (sub_from n e)" by simp
lemma "subst (Succ n) e x = Succ (subst n e x)" by simp
lemma "typecheck env n Nat ==> typecheck env (Succ n) Nat" by (simp add: safe_type_subst_def)

lemma "is_val (Succ n) = is_val n" by simp
lemma "eval n n' ==> eval (Succ n) (Succ n')" by simp

abbreviation IsZ :: "expr => expr => expr => expr"
where "IsZ et e0 e1 == Case (Unfold et) (incr_from 0 e0) e1"

lemma "free_vars (IsZ et e0 e1) = free_vars e0 Un free_vars et Un redr_set (free_vars e1)" by auto
lemma "incr_from n (IsZ et e0 e1) = IsZ (incr_from n et) (incr_from n e0) (incr_from (Suc n) e1)" by simp
lemma "n ~: free_vars (IsZ et e0 e1) ==> sub_from n (IsZ et e0 e1) = IsZ (sub_from n et) (sub_from n e0) (sub_from (Suc n) e1)" by simp
lemma "subst (IsZ et e0 e1) e x = IsZ (subst et e x) (subst e0 e x) (subst e1 (incr_from 0 e) (Suc x))" by simp
lemma "typecheck env et Nat ==> typecheck env e0 t ==> typecheck (extend_at env 0 Nat) e1 t ==> typecheck env (IsZ et e0 e1) t" 
proof -
  assume "typecheck env et Nat" 
     and "typecheck env e0 t" 
     and "typecheck (extend_at env 0 Nat) e1 t"
  moreover hence "typecheck env (Unfold et) (safe_type_subst (Sum Unit (Tyvar 0)) (Rec (Sum Unit (Tyvar 0))))" by simp
  ultimately show "typecheck env (Case (Unfold et) (incr_from 0 e0) e1) t" by (simp add: safe_type_subst_def)
qed
lemma "is_val (IsZ e0 e1 e2) = False" by simp
lemma "eval e e' ==> eval (IsZ e e0 e1) (IsZ e' e0 e1)" by simp
lemma "EX e'. eval (IsZ Zero e0 e1) e' & eval e' e0" 
proof -
  have "eval (Case (InL Unit Nat Triv) (incr_from 0 e0) e1) (safe_subst (incr_from 0 e0) Triv)" by (metis ecs2 is_val.simps(5))
  hence "eval (Case (InL Unit Nat Triv) (incr_from 0 e0) e1) e0" by simp
  moreover have "eval (Case (Unfold (Fold (Sum Unit (Tyvar 0)) (InL Unit Nat Triv))) (incr_from 0 e0) e1) (Case (InL Unit Nat Triv) (incr_from 0 e0) e1)" by simp
  ultimately have "EX e'. eval (Case (Unfold (Fold (Sum Unit (Tyvar 0)) (InL Unit Nat Triv))) (incr_from 0 e0) e1) e' & eval e' e0" by fast
  thus "EX e'. eval (IsZ Zero e0 e1) e' & eval e' e0" by simp
qed
lemma "is_val e ==> EX e'. eval (IsZ (Succ e) e0 e1) e' & eval e' (safe_subst e1 e)" 
proof -
  assume X: "is_val e"
  hence "eval (Case (Unfold (Fold (Sum Unit (Tyvar 0)) (InR Unit Nat e))) (incr_from 0 e0) e1) (Case (InR Unit Nat e) (incr_from 0 e0) e1)" by simp
  moreover with X have "eval (Case (InR Unit Nat e) (incr_from 0 e0) e1) (safe_subst e1 e)" by simp
  ultimately show "EX e'. eval (IsZ (Succ e) e0 e1) e' & eval e' (safe_subst e1 e)" by auto
qed

lemma canonical_nat_like: "typecheck env e t ==> is_val e ==> 
    (t = Nat --> e = Zero | (EX v. typecheck env v Nat & is_val v & e = Succ v)) & 
    (t = Sum Unit Nat --> e = InL Unit Nat Triv | (EX v. typecheck env v Nat & is_val v & e = InR Unit Nat v))"
by (induction env e t rule: typecheck.induct, auto simp add: canonical_unit safe_type_subst_def) 

lemma canonical_nat: "typecheck env e Nat ==> is_val e ==> e = Zero | (EX v. typecheck env v Nat & is_val v & e = Succ v)"
by (simp add: canonical_nat_like)

end
