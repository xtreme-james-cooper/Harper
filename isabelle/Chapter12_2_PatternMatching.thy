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

end
