theory Chapter12_2_PatternMatching
imports Chapter12_1_Language
begin

type_synonym substitution = "expr list"

primrec apply_subst :: "substitution => expr => expr"
where "apply_subst [] e = e"
    | "apply_subst (s # sig) e = apply_subst sig (subst (mult_insert (length sig) s) e)"

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

datatype constraint = 
  Truth
| Falsity
| And constraint constraint
| Or constraint constraint
| InLCon constraint
| InRCon constraint
| TrivCon
| PairCon constraint constraint

primrec patn_constraint :: "patn => constraint"
where "patn_constraint VarPat = Truth"
    | "patn_constraint WildPat = Truth"
    | "patn_constraint TrivPat = TrivCon"
    | "patn_constraint (PairPat p1 p2) = PairCon (patn_constraint p1) (patn_constraint p2)"
    | "patn_constraint (InLPat p) = InLCon (patn_constraint p)"
    | "patn_constraint (InRPat p) = InRCon (patn_constraint p)"

fun rule_constraint :: "rule => constraint"
where "rule_constraint (Rule p e) = patn_constraint p"

primrec rules_constraint :: "rule list => constraint"
where "rules_constraint [] = Falsity"
    | "rules_constraint (r # rs) = Or (rule_constraint r) (rules_constraint rs)"

inductive satisfies :: "expr => constraint => bool"
where [simp]: "satisfies e Truth"
    | [simp]: "satisfies e c1 ==> satisfies e c2 ==> satisfies e (And c1 c2)"
    | [simp]: "satisfies e c1 ==> satisfies e (Or c1 c2)"
    | [simp]: "satisfies e c2 ==> satisfies e (Or c1 c2)"
    | [simp]: "satisfies e c ==> satisfies (InL t t' e) (InLCon c)"
    | [simp]: "satisfies e c ==> satisfies (InR t t' e) (InRCon c)"
    | [simp]: "satisfies Triv TrivCon"
    | [simp]: "satisfies e1 c1 ==> satisfies e2 c2 ==> satisfies (Pair e1 e2) (PairCon c1 c2)"

inductive_cases [elim!]: "satisfies e Truth"
inductive_cases [elim!]: "satisfies e Falsity"
inductive_cases [elim!]: "satisfies e (And c1 c2)"
inductive_cases [elim!]: "satisfies e (Or c1 c2)"
inductive_cases [elim!]: "satisfies e (InLCon c)"
inductive_cases [elim!]: "satisfies e (InRCon c)"
inductive_cases [elim!]: "satisfies e TrivCon"
inductive_cases [elim!]: "satisfies e (PairCon c1 c2)"

definition satisfies_all :: "constraint => bool"
where "satisfies_all = undefined"

lemma [simp]: "rule_constraint (insert_rule n r) = rule_constraint r"
by (induction r, simp_all)

lemma [simp]: "rules_constraint (insert_rules n rs) = rules_constraint rs"
by (induction rs, simp_all)

lemma [simp]: "rule_constraint (subst_rule n e r) = rule_constraint r"
by (induction r, simp_all)

lemma [simp]: "rules_constraint (subst_rules n e rs) = rules_constraint rs"
by (induction rs, simp_all)

lemma [simp]: "rule_constraint (remove_rule n r) = rule_constraint r"
by (induction r, simp_all)

lemma [simp]: "rules_constraint (remove_rules n rs) = rules_constraint rs"
by (induction rs, simp_all)

lemma [simp]: "satisfies_all c ==> satisfies e c"
by simp sorry

lemma [simp]: "satisfies e (patn_constraint p) ==> (EX s. matches p e s)"
by simp sorry

lemma [simp]: "~ satisfies e (patn_constraint p) ==> no_match p e"
by simp sorry

lemma [elim!]: "satisfies e (Or r1 r2) ==> ~ satisfies e r1 ==> satisfies e r2"
by (induction e "Or r1 r2" rule: satisfies.induct, simp_all)


end
