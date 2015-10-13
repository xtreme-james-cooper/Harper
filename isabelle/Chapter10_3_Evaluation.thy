theory Chapter10_3_Evaluation
imports Chapter10_2_Typechecking
begin

primrec is_val :: "expr \<Rightarrow> bool" where 
  "is_val (Var v) = False"
| "is_val Zero = True"
| "is_val (Suc e) = is_val e"
| "is_val (Iter et e0 es) = False"
| "is_val (Lam t e) = True"
| "is_val (Appl e1 e2) = False"
| "is_val Triv = True"
| "is_val (Pair e1 e2) = (is_val e1 \<and> is_val e2)"
| "is_val (ProjL e) = False"
| "is_val (ProjR e) = False"

inductive eval :: "expr \<Rightarrow> expr \<Rightarrow> bool" where 
  eval_suc [simp]: "eval e e' \<Longrightarrow> eval (Suc e) (Suc e')"
| eval_iter_1 [simp]: "eval et et' \<Longrightarrow> eval (Iter et e0 es) (Iter et' e0 es)"
| eval_iter_2 [simp]: "eval (Iter Zero e0 es) e0"
| eval_iter_3 [simp]: "is_val et \<Longrightarrow> eval (Iter (Suc et) e0 es) (subst (Iter et e0 es) first es)"
| eval_appl_1 [simp]: "eval e1 e1' \<Longrightarrow> eval (Appl e1 e2) (Appl e1' e2)"
| eval_appl_2 [simp]: "is_val e1 \<Longrightarrow> eval e2 e2' \<Longrightarrow> eval (Appl e1 e2) (Appl e1 e2')"
| eval_appl_3 [simp]: "is_val e2 \<Longrightarrow> eval (Appl (Lam t2 e1) e2) (subst e2 first e1)"
| eval_pair_1 [simp]: "eval e1 e1' \<Longrightarrow> eval (Pair e1 e2) (Pair e1' e2)"
| eval_pair_2 [simp]: "is_val e1 \<Longrightarrow> eval e2 e2' \<Longrightarrow> eval (Pair e1 e2) (Pair e1 e2')"
| eval_projl_1 [simp]: "eval e e' \<Longrightarrow> eval (ProjL e) (ProjL e')"
| eval_projl_2 [simp]: "eval (ProjL (Pair e1 e2)) e1"
| eval_projr_1 [simp]: "eval e e' \<Longrightarrow> eval (ProjR e) (ProjR e')"
| eval_projr_2 [simp]: "eval (ProjR (Pair e1 e2)) e2"

lemma canonical_nat: "is_val e \<Longrightarrow> typecheck gam e Nat \<Longrightarrow> e = Zero | (\<exists>e'. e = Suc e')"
  by (induction e) auto

lemma canonical_arrow: "is_val e \<Longrightarrow> typecheck gam e (Arrow t1 t2) \<Longrightarrow> \<exists>e'. e = Lam t1 e'"
  by (induction e) auto

lemma canonical_unit: "is_val e \<Longrightarrow> typecheck gam e Unit \<Longrightarrow> e = Triv"
  by (induction e) auto

lemma canonical_prod: "is_val e \<Longrightarrow> typecheck gam e (Prod t1 t2) \<Longrightarrow> \<exists>e1 e2. e = Pair e1 e2"
  by (induction e) auto

theorem preservation: "eval e e' \<Longrightarrow> typecheck gam e t \<Longrightarrow> typecheck gam e' t"
  by (induction e e' arbitrary: t rule: eval.induct) fastforce+

theorem progress: "typecheck gam e t \<Longrightarrow> gam = empty_env \<Longrightarrow> is_val e \<or> (\<exists>e'. eval e e')"
  proof (induction gam e t rule: typecheck.induct)
  case tc_var
    thus ?case by simp
  next case tc_zero
    thus ?case by simp
  next case tc_suc
    thus ?case by (metis eval_suc is_val.simps(3))
  next case tc_iter
    thus ?case by (metis eval_iter_1 eval_iter_2 eval_iter_3 is_val.simps(3) canonical_nat)
  next case tc_lam
    thus ?case by simp
  next case tc_appl
    thus ?case by (metis eval_appl_1 eval_appl_2 eval_appl_3 canonical_arrow)
  next case tc_triv
    thus ?case by simp
  next case tc_pair
    thus ?case by (metis eval_pair_1 eval_pair_2 is_val.simps(8))
  next case tc_projl
    thus ?case by (metis eval_projl_1 eval_projl_2 canonical_prod)
  next case tc_projr
    thus ?case by (metis eval_projr_1 eval_projr_2 canonical_prod)
  qed

end
