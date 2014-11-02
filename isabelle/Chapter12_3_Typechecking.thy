theory Chapter12_3_Typechecking
imports Chapter12_2_PatternMatching
begin

inductive typecheck_patn :: "patn => type => type env => bool"
where tc_vpat [simp]: "typecheck_patn VarPat t (extend empty_env t)"
    | tc_wpat [simp]: "typecheck_patn WildPat t empty_env"
    | tc_tpat [simp]: "typecheck_patn TrivPat Unit empty_env"
    | tc_ppat [simp]: "typecheck_patn p1 t1 e1 ==> typecheck_patn p2 t2 e2 ==> 
          typecheck_patn (PairPat p1 p2) (Prod t1 t2) (e1 +++ e2)"
    | tc_lpat [simp]: "typecheck_patn p t e ==> typecheck_patn (InLPat p) (Sum t t2) e"
    | tc_rpat [simp]: "typecheck_patn p t e ==> typecheck_patn (InRPat p) (Sum t2 t) e"

inductive_cases [elim!]: "typecheck_patn VarPat t gam"
inductive_cases [elim!]: "typecheck_patn WildPat t gam"
inductive_cases [elim!]: "typecheck_patn TrivPat t gam"
inductive_cases [elim!]: "typecheck_patn (PairPat p1 p2) t gam"
inductive_cases [elim!]: "typecheck_patn (InLPat p) t gam"
inductive_cases [elim!]: "typecheck_patn (InRPat p) t gam"

inductive typecheck :: "type env => expr => type => bool"
      and typecheck_rules :: "type env => type => rule list => type => bool"
      and typecheck_rule :: "type env => type => rule => type => bool"
where tc_var [simp]: "lookup gam x = Some t ==> typecheck gam (Var x) t"
    | tc_zero [simp]: "typecheck gam Zero Nat"
    | tc_suc [simp]: "typecheck gam e Nat ==> typecheck gam (Suc e) Nat"
    | tc_rec [simp]: "typecheck gam et Nat ==> typecheck gam e0 t ==> 
                typecheck (extend (extend gam t) Nat) es t ==> typecheck gam (Rec et e0 es) t"
    | tc_lam [simp]: "typecheck (extend gam t1) e t2 ==> typecheck gam (Lam t1 e) (Arrow t1 t2)"
    | tc_appl [simp]: "typecheck gam e1 (Arrow t2 t) ==> typecheck gam e2 t2 ==> 
                typecheck gam (Appl e1 e2) t"
    | tc_triv [simp]: "typecheck gam Triv Unit"
    | tc_pair [simp]: "typecheck gam e1 t1 ==> typecheck gam e2 t2 ==> 
                typecheck gam (Pair e1 e2) (Prod t1 t2)"
    | tc_projl [simp]: "typecheck gam e (Prod t1 t2) ==> typecheck gam (ProjL e) t1"
    | tc_projr [simp]: "typecheck gam e (Prod t1 t2) ==> typecheck gam (ProjR e) t2"
    | tc_abort [simp]: "typecheck gam e Void ==> typecheck gam (Abort t e) t"
    | tc_case [simp]: "typecheck gam et (Sum t1 t2) ==> typecheck (extend gam t1) el t ==> 
                typecheck (extend gam t2) er t ==> typecheck gam (Case et el er) t"
    | tc_inl [simp]: "typecheck gam e t1 ==> typecheck gam (InL t1 t2 e) (Sum t1 t2)"
    | tc_inr [simp]: "typecheck gam e t2 ==> typecheck gam (InR t1 t2 e) (Sum t1 t2)"
    | tc_match [simp]: "typecheck gam e t1 ==> typecheck_rules gam t1 rs t ==> 
                typecheck gam (Match e rs) t"
    | tc_rules_nil [simp]: "typecheck_rules gam t1 [] t"
    | tc_rules_cons [simp]: "typecheck_rule gam t1 r t ==> typecheck_rules gam t1 rs t ==> 
                typecheck_rules gam t1 (r # rs) t"
    | tc_rule [simp]: "typecheck_patn p t1 gam1 ==> typecheck (gam1 +++ gam) e t ==>
                typecheck_rule gam t1 (Rule p e) t"

inductive_cases [elim!]: "typecheck gam (Var x) t"
inductive_cases [elim!]: "typecheck gam Zero t"
inductive_cases [elim!]: "typecheck gam (Suc e) t"
inductive_cases [elim!]: "typecheck gam (Rec et e0 es) t"
inductive_cases [elim!]: "typecheck gam (Lam t1 e) t"
inductive_cases [elim!]: "typecheck gam (Appl e1 e2) t"
inductive_cases [elim!]: "typecheck gam Triv t"
inductive_cases [elim!]: "typecheck gam (Pair e1 e2) t"
inductive_cases [elim!]: "typecheck gam (ProjL e) t"
inductive_cases [elim!]: "typecheck gam (ProjR e) t"
inductive_cases [elim!]: "typecheck gam (Abort t1 e) t"
inductive_cases [elim!]: "typecheck gam (Case et el er) t"
inductive_cases [elim!]: "typecheck gam (InL t1 t2 e) t"
inductive_cases [elim!]: "typecheck gam (InR t1 t2 e) t"
inductive_cases [elim!]: "typecheck gam (Match e rs) t"
inductive_cases [elim!]: "typecheck_rules gam t1 [] t"
inductive_cases [elim!]: "typecheck_rules gam t1 (r # rs) t"
inductive_cases [elim!]: "typecheck_rule gam t1 (Rule p e) t"

inductive typecheck_subst :: "type env => substitution => type env => bool"
where tc_sub_nil [simp]: "typecheck_subst gam [] empty_env"
    | tc_sub_cons [simp]: "typecheck gam e t ==> typecheck_subst gam es sig ==> 
          typecheck_subst gam (e # es) (extend sig t)"

inductive_cases [elim!]: "typecheck_subst g [] sig"
inductive_cases [elim!]: "typecheck_subst g (e # es) sig"

lemma [simp]: "typecheck_patn p t gam ==> pat_var_count p = env_size gam"
by (induction p t gam rule: typecheck_patn.induct, simp_all)

lemma [simp]: "typecheck gam e t ==> n in gam ==> 
         typecheck (extend_at n gam t') (insert n e) t"
  and [simp]: "typecheck_rules gam tt rs t ==> n in gam ==> 
         typecheck_rules (extend_at n gam t') tt (insert_rules n rs) t"
  and [simp]: "typecheck_rule gam tt r t ==> n in gam ==> 
         typecheck_rule (extend_at n gam t') tt (insert_rule n r) t"
proof (induction gam e t and gam tt rs t and gam tt r t arbitrary: n and n and n 
       rule: typecheck_typecheck_rules_typecheck_rule.inducts, fastforce+)
case (tc_rule p t1 gam1 gam e t)
  hence "(next_by (env_size gam1) n) in (gam1 +++ gam)" by simp
  with tc_rule show ?case by fastforce
qed 

lemma [simp]: "typecheck gam e t ==> typecheck (sig +++ gam) (mult_insert (env_size sig) e) t"
proof (induction "env_size sig" arbitrary: sig)
case 0
  hence "sig = empty_env" by auto
  with 0 show ?case by simp
next case (Suc n)
  from Suc have "env_size sig = Nat.Suc n" by simp
  hence "EX sig' s. sig = extend sig' s & env_size sig' = n" by fast
  then obtain sig' s where SDEF: "sig = extend sig' s & env_size sig' = n" by fast
  with Suc have "typecheck (sig' +++ gam) (mult_insert n e) t" by fast
  hence "typecheck (extend sig' s +++ gam) (insert first (mult_insert n e)) t" by simp
  with Suc SDEF show ?case by (metis mult_insert.simps(2))
qed

lemma [simp]: "typecheck (extend_at n gam t') e t ==> n in gam ==> typecheck gam e' t' ==> 
        typecheck gam (remove n (subst' n (insert n e') e)) t"
  and [simp]: "typecheck_rules (extend_at n gam t') tt rs t ==> n in gam ==> typecheck gam e' t' ==> 
        typecheck_rules  gam tt (remove_rules n (subst_rules n (insert n e') rs)) t"
  and [simp]: "typecheck_rule (extend_at n gam t') tt r t ==> n in gam ==> typecheck gam e' t' ==> 
        typecheck_rule gam tt (remove_rule n (subst_rule n (insert n e') r)) t"
by (induction "extend_at n gam t'" e t and "extend_at n gam t'" tt rs t 
          and "extend_at n gam t'" tt r t 
    arbitrary: n gam t' e' and n gam t' e' and n gam t' e'
    rule: typecheck_typecheck_rules_typecheck_rule.inducts, fastforce+)

lemma [simp]: "typecheck (extend gam t') e t ==> typecheck gam e' t' ==> 
                          typecheck gam (subst e' e) t"
by (simp add: subst_def)

lemma [simp]: "typecheck_subst gam s sig ==> length s = env_size sig"
by (induction gam s sig rule: typecheck_subst.induct, simp_all)

lemma [simp]: "typecheck_subst gg s g ==> typecheck_subst gg s' g' ==> 
        typecheck_subst gg (s @ s') (g +++ g')"
by (induction s g rule: typecheck_subst.induct, simp_all) 

lemma [simp]: "typecheck_subst gam s sig ==> typecheck (sig +++ gam) e t ==> 
        typecheck gam (apply_subst s e) t"
by (induction gam s sig arbitrary: e rule: typecheck_subst.induct, simp_all)

lemma [simp]: "matches p e s ==> typecheck gam e t1 ==> typecheck_patn p t1 sig ==> 
        typecheck_subst gam s sig"
by (induction p e s arbitrary: gam t1 sig rule: matches.induct, auto)

end
