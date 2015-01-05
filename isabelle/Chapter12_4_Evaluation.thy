theory Chapter12_4_Evaluation
imports Chapter12_3_Typechecking
begin

fun is_val :: "expr => bool"
where "is_val (Var v) = False"
    | "is_val Zero = True"
    | "is_val (Suc e) = is_val e"
    | "is_val (Rec et e0 es) = False"
    | "is_val (Lam t e) = True"
    | "is_val (Appl e1 e2) = False"
    | "is_val Triv = True"
    | "is_val (Pair e1 e2) = (is_val e1 & is_val e2)"
    | "is_val (ProjL e) = False"
    | "is_val (ProjR e) = False"
    | "is_val (Abort t e) = False"
    | "is_val (Case et el er) = False"
    | "is_val (InL t1 t2 e) = is_val e"
    | "is_val (InR t1 t2 e) = is_val e"
    | "is_val (Match e rs) = False"

inductive eval :: "expr => expr => bool"
      and eval_rules :: "expr => rule list => expr => bool"
      and eval_rule :: "expr => rule => expr option => bool"
where eval_suc [simp]: "eval e e' ==> eval (Suc e) (Suc e')"
    | eval_rec_1 [simp]: "eval et et' ==> eval (Rec et e0 es) (Rec et' e0 es)"
    | eval_rec_2 [simp]: "eval (Rec Zero e0 es) e0"
    | eval_rec_3 [simp]: "is_val et ==> 
            eval (Rec (Suc et) e0 es) (subst (Rec et e0 es) first (subst et first es))"
    | eval_appl_1 [simp]: "eval e1 e1' ==> eval (Appl e1 e2) (Appl e1' e2)"
    | eval_appl_2 [simp]: "is_val e1 ==> eval e2 e2' ==> eval (Appl e1 e2) (Appl e1 e2')"
    | eval_appl_3 [simp]: "is_val e2 ==> eval (Appl (Lam t2 e1) e2) (subst e2 first e1)"
    | eval_pair_1 [simp]: "eval e1 e1' ==> eval (Pair e1 e2) (Pair e1' e2)"
    | eval_pair_2 [simp]: "is_val e1 ==> eval e2 e2' ==> eval (Pair e1 e2) (Pair e1 e2')"
    | eval_projl_1 [simp]: "eval e e' ==> eval (ProjL e) (ProjL e')"
    | eval_projl_2 [simp]: "eval (ProjL (Pair e1 e2)) e1"
    | eval_projr_1 [simp]: "eval e e' ==> eval (ProjR e) (ProjR e')"
    | eval_projr_2 [simp]: "eval (ProjR (Pair e1 e2)) e2"
    | eval_abort [simp]: "eval e e' ==> eval (Abort t e) (Abort t e')"
    | eval_case_1 [simp]: "eval et et' ==> eval (Case et el er) (Case et' el er)"
    | eval_case_2 [simp]: "is_val e ==> eval (Case (InL t1 t2 e) el er) (subst e first el)"
    | eval_case_3 [simp]: "is_val e ==> eval (Case (InR t1 t2 e) el er) (subst e first er)"
    | eval_inl [simp]: "eval e e' ==> eval (InL t1 t2 e) (InL t1 t2 e')"
    | eval_inr [simp]: "eval e e' ==> eval (InR t1 t2 e) (InR t1 t2 e')"
    | eval_match_1 [simp]: "eval e e' ==> eval (Match e rs) (Match e' rs)"
    | eval_match_2 [simp]: "is_val e ==> eval_rules e rs e' ==> eval (Match e rs) e'"
    | eval_rules_1 [simp]: "is_val e ==> eval_rule e r (Some e') ==> eval_rules e (r # rs) e'"
    | eval_rules_2 [simp]: "is_val e ==> eval_rule e r None ==> eval_rules e rs e' ==> 
            eval_rules e (r # rs) e'"
    | eval_rule_1 [simp]: "is_val e ==> matches p e s ==> 
            eval_rule e (Rule p e') (Some (apply_subst s e'))"
    | eval_rule_2 [simp]: "is_val e ==> no_match p e ==> eval_rule e (Rule p e2) None"

lemma canonical_nat: "is_val e ==> typecheck gam e Nat ==> 
          e = Zero | (EX e'. e = Suc e' & typecheck gam e' Nat)"
by (induction e, auto)

lemma canonical_nat_no_vars: "is_val e ==> typecheck gam e Nat ==> typecheck gam' e Nat"
by (induction e, auto) 

lemma canonical_arrow: "is_val e ==> typecheck gam e (Arrow t1 t2) ==> 
              EX e'. e = Lam t1 e' & typecheck (extend gam t1) e' t2"
by (induction e, auto)

lemma canonical_unit: "is_val e ==> typecheck gam e Unit ==> e = Triv"
by (induction e, auto)

lemma canonical_prod: "is_val e ==> typecheck gam e (Prod t1 t2) ==> 
              EX e1 e2. e = Pair e1 e2 & typecheck gam e1 t1 & typecheck gam e2 t2"
by (induction e, auto)

lemma canonical_void: "is_val e ==> typecheck gam e Void ==> False"
by (induction e, auto)

lemma canonical_sum: "is_val e ==> typecheck gam e (Sum t1 t2) ==> 
          (EX e'. e = InL t1 t2 e' & typecheck gam e' t1) | 
          (EX e'. e = InR t1 t2 e' & typecheck gam e' t2)"
by (induction e, auto)

lemma "typecheck_patn p t sig ==> typecheck gam e t ==> is_val e ==> 
          (EX s. matches p e s & typecheck_subst gam s sig) | no_match p e" 
proof (induction p t sig arbitrary: e gam rule: typecheck_patn.induct)
case tc_vpat
  thus ?case by (metis matches.intros(1) typecheck_subst.intros(1) typecheck_subst.intros(2))
next case tc_wpat
  thus ?case by (metis matches.intros(2) typecheck_subst.intros(1))
next case tc_tpat
  thus ?case by (metis canonical_unit matches.intros(3) typecheck_subst.intros(1))
next case (tc_ppat p1 t1 s1 p2 t2 s2)
  then obtain e1 e2 where E1E2: "e = Pair e1 e2 & typecheck gam e1 t1 & typecheck gam e2 t2" by (metis canonical_prod)
  thus ?case proof (cases "no_match p1 e1")
  case True
    with E1E2 show ?thesis by (metis no_match.intros(2))
  next case False
    with tc_ppat E1E2 obtain s where SDEF: "matches p1 e1 s \<and> typecheck_subst gam s s1" by fastforce
    thus ?thesis proof (cases "no_match p2 e2")
    case True
      with E1E2 show ?thesis by (metis no_match.intros(3))
    next case False
      with tc_ppat E1E2 obtain s' where "matches p2 e2 s' \<and> typecheck_subst gam s' s2" by fastforce
      with SDEF have "matches (PairPat p1 p2) (Pair e1 e2) (s @ s') & typecheck_subst gam (s @ s') (s1 +++ s2)" by simp
      with E1E2 show ?thesis by metis
    qed
  qed
next case tc_lpat
  thus ?case by (metis canonical_sum expr.distinct(206) expr.inject(11) is_val.simps(13) 
                 matches.intros(5) no_match.intros(5) no_match.intros(6))
next case tc_rpat
  thus ?case by (metis canonical_sum expr.distinct(206) expr.inject(12) is_val.simps(14) 
                 matches.intros(6) no_match.intros(7) no_match.intros(8))
qed

theorem preservation: "eval e e' ==> typecheck gam e t ==> typecheck gam e' t"
    and "eval_rules e rs e' ==> typecheck gam e tt ==> typecheck_rules gam tt rs t ==> 
            typecheck gam e' t"
    and "eval_rule e r oe' ==> oe' = Some e' ==> typecheck gam e tt ==> typecheck_rule gam tt r t ==> 
            typecheck gam e' t"
proof (induction e e' and e rs e' and e r oe' arbitrary: t and tt t and tt t e'
       rule: eval_eval_rules_eval_rule.inducts)
case eval_suc 
  thus ?case by fastforce
next case eval_rec_1 
  thus ?case by fastforce
next case eval_rec_2 
  thus ?case by fastforce
next case (eval_rec_3 et e0 es)
  from eval_rec_3 canonical_nat_no_vars have "typecheck (extend gam t) (subst et first es) t" by auto
  with eval_rec_3 show ?case by fastforce
next case eval_appl_1 
  thus ?case by fastforce
next case eval_appl_2 
  thus ?case by fastforce
next case eval_appl_3 
  thus ?case by fastforce
next case eval_pair_1 
  thus ?case by fastforce
next case eval_pair_2 
  thus ?case by fastforce
next case eval_projl_1 
  thus ?case by fastforce
next case eval_projl_2 
  thus ?case by fastforce
next case eval_projr_1 
  thus ?case by fastforce
next case eval_projr_2 
  thus ?case by fastforce
next case eval_abort
  thus ?case by fastforce
next case eval_case_1 
  thus ?case by fastforce
next case eval_case_2 
  thus ?case by fastforce
next case eval_case_3 
  thus ?case by fastforce
next case eval_inl
  thus ?case by fastforce
next case eval_inr
  thus ?case by fastforce
next case eval_match_1
  thus ?case by fastforce
next case eval_match_2
  thus ?case by fastforce
next case eval_rules_1
  thus ?case by fastforce
next case eval_rules_2
  thus ?case by fastforce
next case (eval_rule_1 e p s e'' tt)
  then obtain sig where SIG: "typecheck_patn p tt sig & typecheck (sig +++ gam) e'' t" by fast
  from eval_rule_1 SIG have "typecheck_subst gam s sig" by simp
  with SIG have "typecheck gam (apply_subst s e'') t" by simp
  with eval_rule_1 show ?case by simp
next case eval_rule_2
  thus ?case by fastforce
qed

theorem progress: "typecheck gam e t ==> gam = empty_env ==> is_val e | (EX e'. eval e e')"
    and "typecheck_rules gam tt rs t ==> is_val e ==> satisfies e (rules_constraint rs) ==> 
            typecheck gam e tt ==> gam = empty_env ==> EX e'. eval_rules e rs e'"
    and "typecheck_rule gam tt r t ==> is_val e ==> typecheck gam e tt ==> gam = empty_env ==> 
              (satisfies e (rule_constraint r) --> (EX e'. eval_rule e r (Some e'))) & 
              (~ satisfies e (rule_constraint r) --> eval_rule e r None)"
proof (induction gam e t and gam tt rs t and gam tt r t arbitrary: and e and e rs
       rule: typecheck_typecheck_rules_typecheck_rule.inducts)
case tc_var
  thus ?case by simp
next case tc_zero
  thus ?case by simp
next case tc_suc
  thus ?case by (metis eval_suc is_val.simps(3))
next case tc_rec
  thus ?case by (metis eval_rec_1 eval_rec_2 eval_rec_3 is_val.simps(3) canonical_nat)
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
next case tc_abort
  thus ?case by (metis eval_abort canonical_void)
next case tc_case
  thus ?case 
  by (metis eval_case_1 eval_case_2 eval_case_3 is_val.simps(13) is_val.simps(14) canonical_sum)
next case tc_inl
  thus ?case by (metis eval_inl is_val.simps(13))
next case tc_inr
  thus ?case by (metis eval_inr is_val.simps(14))
next case (tc_match gam e t1 rs t)
  thus ?case
  proof (cases "is_val e")
  case False
    with tc_match show ?thesis by (metis eval_match_1)
  next case True
    with tc_match have "EX a. eval_rules e rs a" by simp
    with True show ?thesis by (metis eval_match_2)
  qed
next case tc_rules_nil
  thus ?case by auto
next case (tc_rules_cons gam t1 r t rs)
  thus ?case
  proof (cases "satisfies e (rule_constraint r)")
  case True
    with tc_rules_cons show ?thesis by (metis eval_rules_1)
  next case False
    from tc_rules_cons have "satisfies e (rules_constraint (r # rs))" by simp
    with False have "satisfies e (rules_constraint rs)" by force
    with tc_rules_cons False show ?thesis by (metis eval_rules_2)
  qed
next case (tc_rule p t1 sig gam e' t)
  thus ?case
  proof auto
    assume V: "is_val e" and "satisfies e (patn_constraint p)"
    hence "EX s. matches p e s" by simp
    with V show "EX a. eval_rule e (Rule p e') (Some a)" by (metis eval_rule_1)
  qed
qed

end
