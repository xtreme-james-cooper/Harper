theory Vars
imports Main
begin

datatype var = VAR nat

primrec get_free_var' :: "var set => nat => nat"
where "get_free_var' vs 0 = 0"
    | "get_free_var' vs (Suc n) = (if VAR (Suc n) : vs 
                                   then get_free_var' (vs - {VAR (Suc n)}) n 
                                   else Suc n)"

lemma [simp]: "get_free_var' vs n <= n"
proof (induction n arbitrary: vs)
case 0
  thus ?case by simp
next case (Suc n)
  thus ?case
  proof (cases "VAR (Suc n) : vs")
  case True
    from Suc have "get_free_var' (vs - {VAR (Suc n)}) n <= n" by simp
    with True show ?thesis by auto
  next case False
    thus ?thesis by simp
  qed
qed

lemma [simp]: "finite vs ==> n = card vs ==> VAR (get_free_var' vs n) ~: vs"
proof (induction n arbitrary: vs)
case 0
  thus ?case by simp
next case (Suc n)
  thus ?case
  proof (cases "VAR (Suc n) : vs")
  case True
    from True Suc have "n = card (vs - {VAR (Suc n)})" by simp
    with Suc have "VAR (get_free_var' (vs - {VAR (Suc n)}) n) ~: vs - {VAR (Suc n)}" by auto
    moreover have "VAR (get_free_var' (vs - {VAR (Suc n)}) n) ~: {VAR (Suc n)}" 
    proof auto
      assume "get_free_var' (vs - {VAR (Suc n)}) n = Suc n"
      moreover have "get_free_var' (vs - {VAR (Suc n)}) n <= n" by simp
      ultimately show False by simp
    qed
    ultimately have "VAR (get_free_var' (vs - {VAR (Suc n)}) n) ~: vs" by simp
    with True show ?thesis by simp
  next case False
    thus ?thesis by simp
  qed
qed


definition get_free_var :: "var set => var"
where "get_free_var vs = VAR (get_free_var' vs (card vs))"

lemma [simp]: "finite vs ==> get_free_var vs ~: vs"
by (simp add: get_free_var_def)

end
