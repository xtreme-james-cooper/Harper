theory Chapter12_3_PatternMatching
imports Chapter12_2_Typechecking
begin

type_synonym substitution = "expr list"

primrec apply_subst :: "substitution => expr => expr"
where "apply_subst [] e = e"
    | "apply_subst (s # sig) e = apply_subst sig (subst (mult_insert (length sig) s) e)"

inductive typecheck_subst :: "type env => substitution => type env => bool"
where tc_sub_nil [simp]: "typecheck_subst gam [] empty_env"
    | tc_sub_cons [simp]: "typecheck gam e t ==> typecheck_subst gam es sig ==> 
          typecheck_subst gam (e # es) (extend sig t)"

inductive_cases [elim!]: "typecheck_subst g [] sig"
inductive_cases [elim!]: "typecheck_subst g (e # es) sig"

inductive matches :: "patn => expr => substitution => bool"
where [simp]: "matches VarPat e [e]"
    | [simp]: "matches WildPat e []"
    | [simp]: "matches TrivPat Triv []"
    | [simp]: "matches p1 e1 s1 ==> matches p2 e2 s2 ==> 
                  matches (PairPat p1 p2) (Pair e1 e2) (s1 @ s2)"
    | [simp]: "matches p e s ==> matches (InLPat p) (InL t t' e) s"
    | [simp]: "matches p e s ==> matches (InRPat p) (InR t t' e) s"

inductive_cases [elim!]: "matches VarPat e s"
inductive_cases [elim!]: "matches WildPat e s"
inductive_cases [elim!]: "matches TrivPat e s"
inductive_cases [elim!]: "matches (PairPat p1 p2) e s"
inductive_cases [elim!]: "matches (InLPat p) e s"
inductive_cases [elim!]: "matches (InRPat p) e s"

inductive no_match :: "patn => expr => bool"
where "no_match p1 e1 ==> no_match (PairPat p1 p2) (Pair e1 e2)"
    | "no_match p2 e2 ==> no_match (PairPat p1 p2) (Pair e1 e2)"
    | "no_match (InLPat p) (InR t t' e)"
    | "no_match p e ==> no_match (InLPat p) (InL t t' e)"
    | "no_match (InRPat p) (InL t t' e)"
    | "no_match p e ==> no_match (InRPat p) (InR t t' e)"

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
