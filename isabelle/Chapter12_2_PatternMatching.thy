theory Chapter12_2_PatternMatching
imports Chapter12_1_Language Utilities
begin

type_synonym substitution = "expr list"

primrec apply_subst :: "substitution => expr => expr"
where "apply_subst [] e = e"
    | "apply_subst (s # sig) e = apply_subst sig (subst (mult_insert (length sig) s) first e)"

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
where "e ~= Triv ==> no_match TrivPat e"
    | "no_match p1 e1 ==> no_match (PairPat p1 p2) (Pair e1 e2)"
    | "no_match p2 e2 ==> no_match (PairPat p1 p2) (Pair e1 e2)"
    | "~ (EX e1 e2. e = Pair e1 e2) ==> no_match (PairPat p1 p2) e"
    | "no_match p e ==> no_match (InLPat p) (InL t t' e)"
    | "~ (EX e' t1 t2. e = InL t1 t2 e') ==> no_match (InLPat p) e"
    | "no_match p e ==> no_match (InRPat p) (InR t t' e)"
    | "~ (EX e' t1 t2. e = InR t1 t2 e') ==> no_match (InRPat p) e"

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

primrec negate :: "constraint => constraint"
where "negate Truth = Falsity"
    | "negate Falsity = Truth"
    | "negate (And c1 c2) = Or (negate c1) (negate c2)"
    | "negate (Or c1 c2) = And (negate c1) (negate c2)"
    | "negate (InLCon c) = Or (InLCon (negate c)) (InRCon Truth)"
    | "negate (InRCon c) = Or (InRCon (negate c)) (InLCon Truth)"    
    | "negate TrivCon = Falsity"
    | "negate (PairCon c1 c2) = Or (PairCon (negate c1) c2) 
                                   (Or (PairCon c1 (negate c2)) 
                                       (PairCon (negate c1) (negate c2)))"

primrec and_count :: "constraint => nat"
where "and_count Truth = 1"
    | "and_count Falsity = 1"
    | "and_count (And c1 c2) = and_count c1 + and_count c2 + 1"
    | "and_count (Or c1 c2) = and_count c1 + and_count c2"
    | "and_count (InLCon c) = and_count c"
    | "and_count (InRCon c) = and_count c"    
    | "and_count TrivCon = 1"
    | "and_count (PairCon c1 c2) = and_count c1 + and_count c2"

primrec collect_inls :: "constraint => constraint option"
where "collect_inls Truth = Some Truth"
    | "collect_inls Falsity = Some Falsity"
    | "collect_inls (And c1 c2) = (case collect_inls c1 of
          None => None
        | Some c1' => case collect_inls c2 of
            None => None
          | Some c2' => Some (And c1' c2'))"
    | "collect_inls (Or c1 c2) = (case collect_inls c1 of
          None => None
        | Some c1' => case collect_inls c2 of
            None => None
          | Some c2' => Some (Or c1' c2'))"
    | "collect_inls (InLCon c) = Some c"
    | "collect_inls (InRCon c) = None"    
    | "collect_inls TrivCon = None"
    | "collect_inls (PairCon c1 c2) = None"

primrec collect_inrs :: "constraint => constraint option"
where "collect_inrs Truth = Some Truth"
    | "collect_inrs Falsity = Some Falsity"
    | "collect_inrs (And c1 c2) = (case collect_inrs c1 of
          None => None
        | Some c1' => case collect_inrs c2 of
            None => None
          | Some c2' => Some (And c1' c2'))"
    | "collect_inrs (Or c1 c2) = (case collect_inrs c1 of
          None => None
        | Some c1' => case collect_inrs c2 of
            None => None
          | Some c2' => Some (Or c1' c2'))"
    | "collect_inrs (InLCon c) = None"
    | "collect_inrs (InRCon c) = Some c"    
    | "collect_inrs TrivCon = None"
    | "collect_inrs (PairCon c1 c2) = None"

function is_incon :: "constraint list => bool"
where "is_incon [] = False"
    | "is_incon (Truth # cs) = is_incon cs"
    | "is_incon (Falsity # cs) = True"
    | "is_incon (And c1 c2 # cs) = is_incon (c1 # c2 # cs)"
    | "is_incon (Or c1 c2 # cs) = (is_incon (c1 # cs) & is_incon (c2 # cs))"
    | "is_incon (InLCon c # cs) = (case collect_map collect_inls cs of
          None => True
        | Some ils => is_incon (c # ils))"
    | "is_incon (InRCon c # cs) = (case collect_map collect_inrs cs of
          None => True
        | Some ils => is_incon (c # ils))"    
    | "is_incon (TrivCon # cs) = is_incon cs"
    | "is_incon (PairCon c1 c2 # cs) = undefined"
by pat_completeness auto

definition satisfies_all :: "constraint => bool"
where "satisfies_all c = is_incon [negate c]"

lemma [simp]: "rule_constraint (insert_rule n r) = rule_constraint r"
by (induction r, simp_all)

lemma [simp]: "rules_constraint (insert_rules n rs) = rules_constraint rs"
by (induction rs, simp_all)

lemma [simp]: "rule_constraint (subst_rule n e r) = rule_constraint r"
by (induction r, simp_all)

lemma [simp]: "rules_constraint (subst_rules n e rs) = rules_constraint rs"
by (induction rs, simp_all)

lemma [simp]: "satisfies e (patn_constraint p) ==> (EX s. matches p e s)"
proof (induction p arbitrary: e)
case WildPat
  thus ?case by (metis matches.intros(2))
next case VarPat
  thus ?case by (metis matches.intros(1))
next case TrivPat
  hence "e = Triv" by auto
  thus ?case by (metis matches.intros(3))
next case (PairPat p1 p2)
  hence "EX e1 e2. e = Pair e1 e2 & satisfies e1 (patn_constraint p1) 
                                  & satisfies e2 (patn_constraint p2)" by auto
  with PairPat show ?case by (metis (full_types) matches.intros(4))
next case (InLPat p)
  hence "EX e' t t'. e = InL t t' e' & satisfies e' (patn_constraint p)" by auto
  with InLPat show ?case by (metis matches.intros(5))
next case (InRPat p)
  hence "EX e' t t'. e = InR t t' e' & satisfies e' (patn_constraint p)" by auto
  with InRPat show ?case by (metis matches.intros(6))
qed

lemma [simp]: "~ satisfies e (patn_constraint p) ==> no_match p e"
proof (induction p arbitrary: e)
case WildPat
  thus ?case by simp
next case VarPat
  thus ?case by simp
next case TrivPat
  hence "e ~= Triv" by auto
  thus ?case by (metis no_match.intros(1))
next case (PairPat p1 p2)
  hence "~ (EX e1 e2. e = Pair e1 e2) |
           (EX e1 e2. e = Pair e1 e2 & (~ satisfies e1 (patn_constraint p1) |
                                        ~ satisfies e2 (patn_constraint p2)))" by auto
  thus ?case by (metis PairPat(1) PairPat(2) no_match.intros(2) no_match.intros(3) no_match.intros(4))
next case (InLPat p)
  hence "~ (EX e' t t'. e = InL t t' e') | 
           (EX e' t t'. e = InL t t' e' & ~ satisfies e' (patn_constraint p))" by auto
  with InLPat show ?case by (metis no_match.intros(5) no_match.intros(6))
next case (InRPat p)
  hence "~ (EX e' t t'. e = InR t t' e') | 
           (EX e' t t'. e = InR t t' e' & ~ satisfies e' (patn_constraint p))" by auto
  with InRPat show ?case by (metis no_match.intros(7) no_match.intros(8))
qed

lemma [elim!]: "satisfies e (Or r1 r2) ==> ~ satisfies e r1 ==> satisfies e r2"
by (induction e "Or r1 r2" rule: satisfies.induct, simp_all)

lemma [simp]: "size (collect_inls c) <= size c"
proof (induction c)
case Truth
  thus ?case by simp
next case Falsity
  thus ?case by simp
next case (And c1 c2)
  thus ?case by (cases "collect_inls c1", simp, cases "collect_inls c2", fastforce+)
next case (Or c1 c2)
  thus ?case by (cases "collect_inls c1", simp, cases "collect_inls c2", fastforce+)
next case InLCon
  thus ?case by simp
next case InRCon
  thus ?case by simp
next case TrivCon
  thus ?case by simp
next case PairCon
  thus ?case by simp
qed

lemma [simp]: "collect_inls c = Some c' ==> and_count c' <= and_count c"
proof (induction c arbitrary: c')
case Truth
  thus ?case by simp
next case Falsity
  thus ?case by simp
next case (And c1 c2)
  thus ?case by (cases "collect_inls c1", simp, cases "collect_inls c2", fastforce+)
next case (Or c1 c2)
  thus ?case by (cases "collect_inls c1", simp, cases "collect_inls c2", fastforce+)
next case InLCon
  thus ?case by simp
next case InRCon
  thus ?case by simp
next case TrivCon
  thus ?case by simp
next case PairCon
  thus ?case by simp
qed

lemma [simp]: "size (collect_inrs c) <= size c"
proof (induction c)
case Truth
  thus ?case by simp
next case Falsity
  thus ?case by simp
next case (And c1 c2)
  thus ?case by (cases "collect_inrs c1", simp, cases "collect_inrs c2", fastforce+)
next case (Or c1 c2)
  thus ?case by (cases "collect_inrs c1", simp, cases "collect_inrs c2", fastforce+)
next case InLCon
  thus ?case by simp
next case InRCon
  thus ?case by simp
next case TrivCon
  thus ?case by simp
next case PairCon
  thus ?case by simp
qed

lemma [simp]: "collect_inrs c = Some c' ==> and_count c' <= and_count c"
proof (induction c arbitrary: c')
case Truth
  thus ?case by simp
next case Falsity
  thus ?case by simp
next case (And c1 c2)
  thus ?case by (cases "collect_inrs c1", simp, cases "collect_inrs c2", fastforce+)
next case (Or c1 c2)
  thus ?case by (cases "collect_inrs c1", simp, cases "collect_inrs c2", fastforce+)
next case InLCon
  thus ?case by simp
next case InRCon
  thus ?case by simp
next case TrivCon
  thus ?case by simp
next case PairCon
  thus ?case by simp
qed

termination is_incon
proof (relation "measures [mapsum and_count, mapsum size]", auto)
  fix cs a
  assume "collect_map collect_inls cs = Some a" 
     and "\<not> mapsum and_count a < mapsum and_count cs"
  show "mapsum and_count a = mapsum and_count cs" by simp sorry
next
  fix cs a
  assume "collect_map collect_inls cs = Some a" 
     and "\<not> mapsum and_count a < mapsum and_count cs"
  show "mapsum size a < Nat.Suc (mapsum size cs)" by simp sorry
next
  fix cs a
  assume "collect_map collect_inrs cs = Some a" 
     and "\<not> mapsum and_count a < mapsum and_count cs"
  show "mapsum and_count a = mapsum and_count cs" by simp sorry
next
  fix cs a
  assume "collect_map collect_inrs cs = Some a" 
     and "\<not> mapsum and_count a < mapsum and_count cs"
  show "mapsum size a < Nat.Suc (mapsum size cs)" by simp sorry
qed

lemma [simp]: "satisfies_all c ==> satisfies e c"
apply (induction c arbitrary: e)
apply (simp_all add: satisfies_all_def)
by (simp add: satisfies_all_def) sorry

end
