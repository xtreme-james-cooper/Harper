theory Chapter11_4_Abbreviations
imports Chapter11_3_Evaluation
begin

(* booleans *)

abbreviation Bool :: type where
  "Bool \<equiv> Sum Unit Unit"

abbreviation Tru :: expr where
  "Tru \<equiv> InL Unit Unit Triv"

abbreviation Fls :: expr where
  "Fls \<equiv> InR Unit Unit Triv"

abbreviation If :: "expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr" where
  "If e et ef \<equiv> Case e (insert first et) (insert first ef)"

lemma tc_true: "typecheck gam Tru Bool"
  by simp

lemma tc_fals: "typecheck gam Fls Bool"
  by simp

lemma tc_if: "typecheck gam e Bool \<Longrightarrow> typecheck gam et t \<Longrightarrow> typecheck gam ef t \<Longrightarrow> 
    typecheck gam (If e et ef) t"
  by simp

lemma [simp]: "is_val Tru"
  by simp

lemma [simp]: "is_val Fls"
  by simp

lemma [simp]: "\<not> is_val (If e et ef)"
  by simp

lemma eval_if_1: "eval e e' \<Longrightarrow> eval (If e et ef) (If e' et ef)"
  by simp

lemma eval_if_2: "eval (If Tru et ef) et"
  proof -
    from eval_case_2 is_val.simps(7) have "eval (Case (InL Unit Unit Triv) (insert first et) 
      (insert first ef)) (subst Triv first (insert first et))" by blast
    thus "eval (If Tru et ef) et" by simp
  qed

lemma eval_if_3: "eval (If Fls et ef) ef"
  proof -
    from eval_case_3 is_val.simps(7) have "eval (Case (InR Unit Unit Triv) (insert first et) 
      (insert first ef)) (subst Triv first (insert first ef))" by blast
    thus "eval (If Fls et ef) ef" by simp
  qed

(* options *)

abbreviation Option :: "type \<Rightarrow> type" where
  "Option \<equiv> Sum Unit"

abbreviation Null :: "type \<Rightarrow> expr" where
  "Null t \<equiv> InL Unit t Triv"

abbreviation Just :: "type \<Rightarrow> expr \<Rightarrow> expr" where
  "Just t e \<equiv> InR Unit t e"

abbreviation Which :: "expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr" where
  "Which e e0 ej \<equiv> Case e (insert first e0) ej"

lemma tc_null: "typecheck gam (Null t) (Option t)"
  by simp

lemma tc_just: "typecheck gam e t \<Longrightarrow> typecheck gam (Just t e) (Option t)"
  by simp

lemma tc_which: "typecheck gam e (Option t) \<Longrightarrow> typecheck gam e0 tt \<Longrightarrow> 
    typecheck (extend gam t) ej tt \<Longrightarrow> typecheck gam (Which e e0 ej) tt"
  by simp

lemma [simp]: "is_val (Null t)"
  by simp

lemma [simp]: "is_val (Just t e) = is_val e"
  by simp

lemma [simp]: "\<not> is_val (Which e e0 ej)"
  by simp

lemma eval_which_1: "eval e e' \<Longrightarrow> eval (Which e e0 ej) (Which e' e0 ej)"
  by simp

lemma eval_which_2: "eval (Which (Null t) e0 ej) e0"
  proof -
    from eval_case_2 is_val.simps(7) have "eval (Case (InL Unit t Triv) (insert first e0) ej) 
      (subst Triv first (insert first e0))" by blast
    thus "eval (Which (Null t) e0 ej) e0" by simp
  qed

lemma eval_which_3: "is_val e \<Longrightarrow> eval (Which (Just t e) e0 ej) (subst e first ej)"
  by simp

end