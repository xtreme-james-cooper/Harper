theory Chapter13_3_PatternMatching
imports Chapter13_2_Typechecking
begin

fun is_val :: "expr => bool"
where "is_val (Var v) = False"
    | "is_val Zero = True"
    | "is_val (Succ n) = is_val n"
    | "is_val (IsZ e0 e1 et) = False"
    | "is_val (Lam t b) = True"
    | "is_val (Ap e1 e2) = False"
    | "is_val (Fix t b) = False"
    | "is_val Triv = True"
    | "is_val (Pair e1 e2) = (is_val e1 & is_val e2)"
    | "is_val (ProjL e) = False"
    | "is_val (ProjR e) = False"
    | "is_val (Abort t e) = False"
    | "is_val (InL t t' e) = is_val e"
    | "is_val (InR t t' e) = is_val e"
    | "is_val (Match e t rs) = False"

lemma canonical_nat: "typecheck env e Nat ==> is_val e ==> e = Zero | (EX v. typecheck env v Nat & is_val v & e = Succ v)"
by (induction e, auto)

lemma canonical_arr: "typecheck env e (Arr t1 t2) ==> is_val e ==> (EX v. e = Lam t1 v & typecheck (extend_at env 0 t1) v t2)"
by (induction e, auto)

lemma canonical_unit: "typecheck env e Unit ==> is_val e ==> e = Triv"
by (induction e, auto)

lemma canonical_prod: "typecheck env e (Prod t1 t2) ==> is_val e ==> (EX e1 e2. e = Pair e1 e2 & typecheck env e1 t1 & typecheck env e2 t2 & is_val e1 & is_val e2)"
by (induction e, auto)

lemma canonical_void: "typecheck env e Void ==> ~ is_val e"
by (induction e, auto)

lemma canonical_sum: "typecheck env e (Sum t1 t2) ==> is_val e ==> 
      (EX e'. e = InL t1 t2 e' & is_val e' & typecheck env e' t1) | (EX e'. e = InR t1 t2 e' & is_val e' & typecheck env e' t2)"
by (induction e, auto)

inductive matches :: "expr list => patn => expr => bool"
where mtchw [simp]: "matches [] Wild e"
    | mtchv [simp]: "matches [e] PVar e"
    | mtcht [simp]: "matches [] PTriv Triv"
    | mtchp [simp]: "matches s1 p1 e1 ==> matches s2 p2 e2 ==> matches (s1 @ s2) (PPair p1 p2) (Pair e1 e2)"
    | mtchl [simp]: "matches s p e ==> matches s (PInL p) (InL t t' e)"
    | mtchr [simp]: "matches s p e ==> matches s (PInR p) (InR t t' e)"

inductive_cases [elim!]: "matches s Wild e"
inductive_cases [elim!]: "matches s PVar e"
inductive_cases [elim!]: "matches s PTriv e"
inductive_cases [elim!]: "matches s (PPair x y) e"
inductive_cases [elim!]: "matches s (PInL x) e"
inductive_cases [elim!]: "matches s (PInR x) e"

inductive no_match :: "expr => patn => bool"
where [simp]: "no_match e1 p1 ==> no_match (Pair e1 e2) (PPair p1 p2)"
    | [simp]: "no_match e2 p2 ==> no_match (Pair e1 e2) (PPair p1 p2)"
    | [simp]: "no_match (InL t t' e) (PInR p)"
    | [simp]: "no_match e p ==> no_match (InL t t' e) (PInL p)"
    | [simp]: "no_match (InR t t' e) (PInL p)"
    | [simp]: "no_match e p ==> no_match (InR t t' e) (PInR p)"

lemma [simp]: "no_match (Pair e1 e2) (PPair p1 p2) ==> no_match e1 p1 | no_match e2 p2"
by (auto, induction "Pair e1 e2" "PPair p1 p2" rule: no_match.induct, auto)

lemma [simp]: "no_match (InL t t' e) (PInL p) = no_match e p"
by (auto, induction "InL t t' e" "PInL p" rule: no_match.induct, simp)

lemma [simp]: "no_match (InR t t' e) (PInR p) = no_match e p"
by (auto, induction "InR t t' e" "PInR p" rule: no_match.induct, simp)

lemma [simp]: "matches s p e ==> ~ no_match e p"
proof (induction s p e rule: matches.induct)
case (mtchw e)
  thus ?case by (auto, induction e Wild rule: no_match.induct)
next case (mtchv e)
  thus ?case by (auto, induction e PVar rule: no_match.induct)
next case mtcht
  thus ?case by (auto, induction Triv PTriv rule: no_match.induct)
next case (mtchp s1 p1 e1 s2 p2 e2)
  thus ?case
  proof auto 
    assume "no_match (Pair e1 e2) (PPair p1 p2)"
       and "matches s1 p1 e1"
       and "matches s2 p2 e2"
       and "~ no_match e1 p1"
       and "~ no_match e2 p2"
    thus False by (induction "Pair e1 e2" "PPair p1 p2" rule: no_match.induct, simp_all)
  qed
next case mtchl
  thus ?case by simp 
next case (mtchr s p e)
  thus ?case by simp 
qed

lemma [simp]: "types_from_pat p t ts ==> typecheck env e t ==> is_val e ==> (EX s. typecheck_subst env s ts & matches s p e) | no_match e p"
proof (induction p t ts arbitrary: e rule: types_from_pat.induct)
case tpwld
  have "typecheck_subst env [] [] & matches [] Wild e" by simp
  hence "EX s. typecheck_subst env s [] & matches s Wild e" by (rule exI)
  thus ?case by simp
next case (tpvar t)
  hence "typecheck_subst env [e] [t] & matches [e] PVar e" by simp
  hence "EX s. typecheck_subst env s [t] & matches s PVar e" by (rule exI)
  thus ?case by simp
next case tptrv
  hence "e = Triv" by (simp add: canonical_unit)
  hence "typecheck_subst env [] [] & matches [] PTriv e" by simp
  hence "EX s. typecheck_subst env s [] \<and> matches s PTriv e" by (rule exI)
  thus ?case by simp
next case (tppar p1 t1 ts1 p2 t2 ts2)
  hence "(EX e1 e2. e = Pair e1 e2 & typecheck env e1 t1 & typecheck env e2 t2 & is_val e1 & is_val e2)" by (simp add: canonical_prod)
  with tppar show ?case
  proof auto
    fix e1 e2 s1 s2
    assume "!!e. typecheck env e t1 ==> is_val e ==> (EX s. typecheck_subst env s ts1 & matches s p1 e) | no_match e p1"
       and "typecheck env e1 t1"
       and "is_val e1"
    hence A: "(EX s. typecheck_subst env s ts1 & matches s p1 e1) | no_match e1 p1" by auto
    assume "!!e. typecheck env e t2 ==> is_val e ==> (EX s. typecheck_subst env s ts2 & matches s p2 e) | no_match e p2"
       and "typecheck env e2 t2"
       and "is_val e2"
    hence B: "(EX s. typecheck_subst env s ts2 & matches s p2 e2) | no_match e2 p2" by auto
    assume C: "~ no_match (Pair e1 e2) (PPair p1 p2)"
    from A C have "EX s. typecheck_subst env s ts1 & matches s p1 e1" by auto
    moreover from B C have "EX s. typecheck_subst env s ts2 & matches s p2 e2" by auto
    ultimately show "EX s. typecheck_subst env s (ts1 @ ts2) & matches s (PPair p1 p2) (Pair e1 e2)"
    proof auto
      fix s1 s2
      assume "typecheck_subst env s1 ts1"
         and "matches s1 p1 e1"
         and "typecheck_subst env s2 ts2"
         and "matches s2 p2 e2"
      hence "typecheck_subst env (s1 @ s2) (ts1 @ ts2) & matches (s1 @ s2) (PPair p1 p2) (Pair e1 e2)" by simp
      thus "EX s. typecheck_subst env s (ts1 @ ts2) & matches s (PPair p1 p2) (Pair e1 e2)" by auto
    qed
  qed
next case (tpinl p t1 ts t2)
  from tpinl have "(EX e'. e = InL t1 t2 e' & is_val e' & typecheck env e' t1) | (EX e'. e = InR t1 t2 e' & is_val e' & typecheck env e' t2)" by (simp add: canonical_sum)
  with tpinl show ?case
  proof (cases "EX e'. e = InL t1 t2 e'", auto)
    fix e'
    assume "!!e. typecheck env e t1 ==> is_val e ==> (EX s. typecheck_subst env s ts & matches s p e) | no_match e p"
       and "~ no_match e' p"
       and "is_val e'"
       and "typecheck env e' t1"
    hence "EX s. typecheck_subst env s ts & matches s p e'" by auto
    thus "EX s. typecheck_subst env s ts & matches s (PInL p) (InL t1 t2 e')" by auto
  qed
next case (tpinr p t2 ts t1)
  from tpinr have "(EX e'. e = InL t1 t2 e' & is_val e' & typecheck env e' t1) | (EX e'. e = InR t1 t2 e' & is_val e' & typecheck env e' t2)" by (simp add: canonical_sum)
  with tpinr show ?case
  proof (cases "EX e'. e = InR t1 t2 e'", auto)
    fix e'
    assume "!!e. typecheck env e t2 ==> is_val e ==> (EX s. typecheck_subst env s ts & matches s p e) | no_match e p"
       and "~ no_match e' p"
       and "is_val e'"
       and "typecheck env e' t2"
    hence "EX s. typecheck_subst env s ts & matches s p e'" by auto
    thus "EX s. typecheck_subst env s ts & matches s (PInR p) (InR t1 t2 e')" by auto
  qed
qed

lemma [simp]: "matches s p e ==> matches s' p e ==> s = s'"
proof (induction s p e arbitrary: s' rule: matches.induct)
case mtchw
  thus ?case by auto 
next case mtchv
  thus ?case by auto 
next case mtcht
  thus ?case by auto 
next case (mtchp s1 p1 e1 s2 p2 e2)
  then obtain s1' s2' where "matches s1' p1 e1 & matches s2' p2 e2 & s1' @ s2' = s'" by auto
  hence "s1 @ s2 = s'"
  proof auto
    assume "matches s1' p1 e1" 
       and "matches s2' p2 e2"
    with mtchp show "s1 @ s2 = s1' @ s2'" by simp
  qed
  thus ?case by simp 
next case (mtchl s p e)
  hence "matches s' p e" by auto
  with mtchl show ?case by simp 
next case (mtchr s p e)
  hence "matches s' p e" by auto
  with mtchr show ?case by simp 
qed

lemma [simp]: "matches s p e ==> typecheck (extend_env ts env) e2 t ==> 
          EX s'. typecheck_subst env s' ts & matches s' p e ==> 
                    typecheck env (apply_subst s e2) t"
proof auto
  fix s'
  assume "matches s p e" 
     and X: "typecheck (extend_env ts env) e2 t" 
     and Y: "typecheck_subst env s' ts" 
     and "matches s' p e"
  moreover hence "s = s'" by simp
  ultimately show "typecheck env (apply_subst s e2) t" by simp
qed 


datatype constr = 
  All
| CInL type type constr
| CInR type type constr
| CTriv
| CPair constr constr

inductive typecheck_constr :: "constr => type => bool"
where tcal [simp]: "typecheck_constr All t"
    | tcil [simp]: "typecheck_constr c t1 ==> typecheck_constr (CInL t1 t2 c) (Sum t1 t2)"
    | tcir [simp]: "typecheck_constr c t2 ==> typecheck_constr (CInR t1 t2 c) (Sum t1 t2)"
    | tctr [simp]: "typecheck_constr CTriv Unit"
    | tcpr [simp]: "typecheck_constr c1 t1 ==> typecheck_constr c2 t2 ==> typecheck_constr (CPair c1 c2) (Prod t1 t2)"

inductive_cases [elim!]: "typecheck_constr All t"
inductive_cases [elim!]: "typecheck_constr (CInL x y z) t"
inductive_cases [elim!]: "typecheck_constr (CInR x y z) t"
inductive_cases [elim!]: "typecheck_constr CTriv t"
inductive_cases [elim!]: "typecheck_constr (CPair x y) t"

inductive extract_constraint :: "patn => type => constr => bool"       
where [simp]: "extract_constraint Wild t All"
    | [simp]: "extract_constraint PVar t All"
    | [simp]: "extract_constraint PTriv Unit CTriv"
    | [simp]: "extract_constraint p1 t1 c1 ==> extract_constraint p2 t2 c2 ==> extract_constraint (PPair p1 p2) (Prod t1 t2) (CPair c1 c2)"
    | [simp]: "extract_constraint p t1 c ==> extract_constraint (PInL p) (Sum t1 t2) (CInL t1 t2 c)"
    | [simp]: "extract_constraint p t2 c ==> extract_constraint (PInR p) (Sum t1 t2) (CInR t1 t2 c)"
 
inductive_cases [elim!]: "extract_constraint Wild t c"
inductive_cases [elim!]: "extract_constraint PVar t c"
inductive_cases [elim!]: "extract_constraint PTriv t c"
inductive_cases [elim!]: "extract_constraint (PPair p1 p2) t c"
inductive_cases [elim!]: "extract_constraint (PInL p) t c"
inductive_cases [elim!]: "extract_constraint (PInR p) t c"

lemma [simp]: "extract_constraint PTriv Unit c ==> c = CTriv"
by (induction PTriv Unit c rule: extract_constraint.induct, simp)

lemma [simp]: "extract_constraint (PPair p1 p2) (Prod t1 t2) c ==> 
      EX c1 c2. extract_constraint p1 t1 c1 & extract_constraint p2 t2 c2 & c = CPair c1 c2"
by (induction "PPair p1 p2" "Prod t1 t2" c rule: extract_constraint.induct, simp)

lemma [simp]: "extract_constraint (PInL p) (Sum t1 t2) c ==> 
      EX c'. extract_constraint p t1 c' & c = CInL t1 t2 c'"
by (induction "PInL p" "Sum t1 t2" c rule: extract_constraint.induct, simp)

lemma [simp]: "extract_constraint (PInR p) (Sum t1 t2) c ==> 
      EX c'. extract_constraint p t2 c' & c = CInR t1 t2 c'"
by (induction "PInR p" "Sum t1 t2" c rule: extract_constraint.induct, simp)

fun get_inls :: "constr list => constr list option"
where "get_inls [] = Some []"
    | "get_inls (All # cs) = None"
    | "get_inls (CInL t1 t2 c # cs) = (case get_inls cs of Some cs' => Some (c # cs') | None => None)"
    | "get_inls (CInR t1 t2 c # cs) = get_inls cs"
    | "get_inls (CTriv # cs) = None"
    | "get_inls (CPair c1 c2 # cs) = None"

fun get_inrs :: "constr list => constr list option"
where "get_inrs [] = Some []"
    | "get_inrs (All # cs) = None"
    | "get_inrs (CInL t1 t2 c # cs) = get_inrs cs"
    | "get_inrs (CInR t1 t2 c # cs) = (case get_inrs cs of Some cs' => Some (c # cs') | None => None)"
    | "get_inrs (CTriv # cs) = None"
    | "get_inrs (CPair c1 c2 # cs) = None"

fun strip_pair_1 :: "constr list => constr list option"
where "strip_pair_1 [] = Some []"
    | "strip_pair_1 (All # cs) = (case strip_pair_1 cs of Some cs' => Some (All # cs') | None => None)"
    | "strip_pair_1 (CInL t1 t2 c # cs) = None"
    | "strip_pair_1 (CInR t1 t2 c # cs) = None"
    | "strip_pair_1 (CTriv # cs) = None"
    | "strip_pair_1 (CPair c1 c2 # cs) = (case strip_pair_1 cs of Some cs' => Some (c1 # cs') | None => None)"

fun strip_pair_2 :: "constr list => constr list option"
where "strip_pair_2 [] = Some []"
    | "strip_pair_2 (All # cs) = (case strip_pair_2 cs of Some cs' => Some (All # cs') | None => None)"
    | "strip_pair_2 (CInL t1 t2 c # cs) = None"
    | "strip_pair_2 (CInR t1 t2 c # cs) = None"
    | "strip_pair_2 (CTriv # cs) = None"
    | "strip_pair_2 (CPair c1 c2 # cs) = (case strip_pair_2 cs of Some cs' => Some (c2 # cs') | None => None)"

lemma [simp]: "Some cs' = get_inls cs ==> list_size size cs' <= list_size size cs"
proof (induction cs arbitrary: cs' rule: get_inls.induct)
case 1
  thus ?case by simp
next case 2
  thus ?case by simp
next case (3 _ _ _ cs)
  thus ?case
  proof (cases "get_inls cs")
  case None
    with 3 show ?thesis by simp
  next case (Some ils)
    with 3 have "list_size size ils <= list_size size cs" by simp
    with 3 Some show ?thesis by simp
  qed
next case (4 _ _ _ cs)
  hence "list_size size cs' <= list_size size cs" by simp
  thus ?case by simp
next case 5
  thus ?case by simp
next case 6
  thus ?case by simp
qed

lemma [simp]: "Some cs' = get_inls cs ==> list_size size cs' <= Suc (n + list_size size cs)"
proof -
  assume "Some cs' = get_inls cs"
  hence "list_size size cs' <= list_size size cs" by simp
  thus "list_size size cs' <= Suc (n + list_size size cs)" by simp
qed

lemma [simp]: "Some cs' = get_inrs cs ==> list_size size cs' <= list_size size cs"
proof (induction cs arbitrary: cs' rule: get_inrs.induct)
case 1
  thus ?case by simp
next case 2
  thus ?case by simp
next case (3 _ _ _ cs)
  from 3 have "list_size size cs' <= list_size size cs" by simp
  thus ?case by simp
next case (4 _ _ _ cs)
  thus ?case
  proof (cases "get_inrs cs")
  case None
    with 4 show ?thesis by simp
  next case (Some irs)
    with 4 have "list_size size irs <= list_size size cs" by simp
    with 4 Some show ?thesis by simp
  qed
next case 5
  thus ?case by simp
next case 6
  thus ?case by simp
qed

lemma [simp]: "Some cs' = get_inrs cs ==> list_size size cs' <= Suc (n + list_size size cs)"
proof -
  assume "Some cs' = get_inrs cs"
  hence "list_size size cs' <= list_size size cs" by simp
  thus "list_size size cs' <= Suc (n + list_size size cs)" by simp
qed

lemma [simp]: "Some cs' = strip_pair_1 cs ==> list_size size cs' <= list_size size cs"
proof (induction cs arbitrary: cs' rule: strip_pair_1.induct)
case 1
  thus ?case by simp
next case (2 cs)
  thus ?case
  proof (cases "strip_pair_1 cs")
  case None
    with 2 show ?thesis by simp
  next case (Some p1s)
    with 2 have "list_size size p1s <= list_size size cs" by simp
    with 2 Some show ?thesis by simp
  qed
next case 3
  thus ?case by simp
next case 4
  thus ?case by simp
next case 5
  thus ?case by simp
next case (6 _ _ cs)
  thus ?case
  proof (cases "strip_pair_1 cs")
  case None
    with 6 show ?thesis by simp
  next case (Some p1s)
    with 6 have "list_size size p1s <= list_size size cs" by simp
    with 6 Some show ?thesis by simp
  qed
qed

lemma [simp]: "Some cs' = strip_pair_2 cs ==> list_size size cs' <= list_size size cs"
proof (induction cs arbitrary: cs' rule: strip_pair_2.induct)
case 1
  thus ?case by simp
next case (2 cs)
  thus ?case
  proof (cases "strip_pair_2 cs")
  case None
    with 2 show ?thesis by simp
  next case (Some p2s)
    from 2 Some have "list_size size p2s <= list_size size cs" by simp
    with 2 Some show ?thesis by simp
  qed
next case 3
  thus ?case by simp
next case 4
  thus ?case by simp
next case 5
  thus ?case by simp
next case (6 _ _ cs)
  thus ?case
  proof (cases "strip_pair_2 cs")
  case None
    with 6 show ?thesis by simp
  next case (Some p1s)
    with 6 have "list_size size p1s <= list_size size cs" by simp
    with 6 Some show ?thesis by simp
  qed
qed

fun perfectly_satisfied :: "constr list => bool"
where "perfectly_satisfied [] = False"
    | "perfectly_satisfied (All # cs) = (cs = [])"
    | "perfectly_satisfied (CInL t1 t2 c # cs) = (case (get_inls cs, get_inrs cs) of
              (Some cls, Some crs) => perfectly_satisfied (c # cls) & perfectly_satisfied crs
            | _ => False)"
    | "perfectly_satisfied (CInR t1 t2 c # cs) = (case (get_inls cs, get_inrs cs) of
              (Some cls, Some crs) => perfectly_satisfied cls & perfectly_satisfied (c # crs)
            | _ => False)"
    | "perfectly_satisfied (CTriv # cs) = (cs = [])"
    | "perfectly_satisfied (CPair c1 c2 # cs) = (case (strip_pair_1 cs, strip_pair_2 cs) of
              (Some c1s, Some c2s) => perfectly_satisfied (c1 # c1s) & perfectly_satisfied (c2 # c2s)
            | _ => False)"

inductive all_matches_complete :: "expr => bool"
      and extract_constraints :: "rule list => type => constr list => bool"
      and extract_constraint_rule :: "rule => type => constr => bool"
where [simp]: "all_matches_complete (Var v)" 
    | [simp]: "all_matches_complete Zero"
    | [simp]: "all_matches_complete e ==> all_matches_complete (Succ e)"
    | [simp]: "all_matches_complete e1 ==> all_matches_complete e2 ==> all_matches_complete e3 ==> all_matches_complete (IsZ e1 e2 e3)"
    | [simp]: "all_matches_complete e ==> all_matches_complete (Lam t' e)"
    | [simp]: "all_matches_complete e1 ==> all_matches_complete e2 ==> all_matches_complete (Ap e1 e2)"
    | [simp]: "all_matches_complete e ==> all_matches_complete (Fix t e)"
    | [simp]: "all_matches_complete Triv"
    | [simp]: "all_matches_complete e1 ==> all_matches_complete e2 ==> all_matches_complete (Pair e1 e2)"
    | [simp]: "all_matches_complete e ==> all_matches_complete (ProjL e)"
    | [simp]: "all_matches_complete e ==> all_matches_complete (ProjR e)"
    | [simp]: "all_matches_complete e ==> all_matches_complete (Abort t e)"
    | [simp]: "all_matches_complete e ==> all_matches_complete (InL t1 t2 e)"
    | [simp]: "all_matches_complete e ==> all_matches_complete (InR t1 t2 e)"
    | [simp]: "all_matches_complete e ==> extract_constraints rs t cs ==> perfectly_satisfied cs ==> all_matches_complete (Match e t rs)"
    | [simp]: "extract_constraints [] t []"
    | [simp]: "extract_constraint_rule r t c1 ==> extract_constraints rs t c2 ==> extract_constraints (r # rs) t (c1 # c2)"
    | [simp]: "extract_constraint p t c ==> all_matches_complete e ==> extract_constraint_rule (Rule p e) t c"

inductive_cases [elim!]: "all_matches_complete (Var x)"
inductive_cases [elim!]: "all_matches_complete Zero"
inductive_cases [elim!]: "all_matches_complete (Succ x)"
inductive_cases [elim!]: "all_matches_complete (IsZ x y z)"
inductive_cases [elim!]: "all_matches_complete (Lam x y)"
inductive_cases [elim!]: "all_matches_complete (Ap x y)"
inductive_cases [elim!]: "all_matches_complete (Fix x y)"
inductive_cases [elim!]: "all_matches_complete Triv"
inductive_cases [elim!]: "all_matches_complete (Pair x y)"
inductive_cases [elim!]: "all_matches_complete (ProjL v)"
inductive_cases [elim!]: "all_matches_complete (ProjR v)"
inductive_cases [elim!]: "all_matches_complete (Abort x y)"
inductive_cases [elim!]: "all_matches_complete (InL x y z)"
inductive_cases [elim!]: "all_matches_complete (InR x y z)"
inductive_cases [elim!]: "all_matches_complete (Match x y z)"
inductive_cases [elim!]: "extract_constraints [] t c"
inductive_cases [elim!]: "extract_constraints (x # y) t c"
inductive_cases [elim!]: "extract_constraint_rule (Rule x y) t c"

end
