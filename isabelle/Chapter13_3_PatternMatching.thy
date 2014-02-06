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
| And constr constr
| Nothing
| Or constr constr
| CInL type type constr
| CInR type type constr
| CTriv
| CPair constr constr

primrec de_morgan_dual :: "constr => constr"
where "de_morgan_dual All = Nothing"
    | "de_morgan_dual (And c1 c2) = Or (de_morgan_dual c1) (de_morgan_dual c2)"
    | "de_morgan_dual Nothing = All"
    | "de_morgan_dual (Or c1 c2) = And (de_morgan_dual c1) (de_morgan_dual c2)"
    | "de_morgan_dual (CInL t1 t2 c) = Or (CInL t1 t2 (de_morgan_dual c)) (CInR t1 t2 All)"
    | "de_morgan_dual (CInR t1 t2 c) = Or (CInR t1 t2 (de_morgan_dual c)) (CInL t1 t2 All)"
    | "de_morgan_dual CTriv = Nothing"
    | "de_morgan_dual (CPair c1 c2) = Or (Or (CPair (de_morgan_dual c1) c2) (CPair c1 (de_morgan_dual c2))) (CPair (de_morgan_dual c1) (de_morgan_dual c2))"

inductive typecheck_constr :: "constr => type => bool"
where tcal [simp]: "typecheck_constr All t"
    | tcan [simp]: "typecheck_constr c1 t ==> typecheck_constr c2 t ==> typecheck_constr (And c1 c2) t"
    | tcno [simp]: "typecheck_constr Nothing t"
    | tcor [simp]: "typecheck_constr c1 t ==> typecheck_constr c2 t ==> typecheck_constr (Or c1 c2) t"
    | tcil [simp]: "typecheck_constr c t1 ==> typecheck_constr (CInL t1 t2 c) (Sum t1 t2)"
    | tcir [simp]: "typecheck_constr c t2 ==> typecheck_constr (CInR t1 t2 c) (Sum t1 t2)"
    | tctr [simp]: "typecheck_constr CTriv Unit"
    | tcpr [simp]: "typecheck_constr c1 t1 ==> typecheck_constr c2 t2 ==> typecheck_constr (CPair c1 c2) (Prod t1 t2)"

inductive_cases [elim!]: "typecheck_constr All t"
inductive_cases [elim!]: "typecheck_constr (And x y) t"
inductive_cases [elim!]: "typecheck_constr Nothing t"
inductive_cases [elim!]: "typecheck_constr (Or x y) t"
inductive_cases [elim!]: "typecheck_constr (CInL x y z) t"
inductive_cases [elim!]: "typecheck_constr (CInR x y z) t"
inductive_cases [elim!]: "typecheck_constr CTriv t"
inductive_cases [elim!]: "typecheck_constr (CPair x y) t"

inductive satisfies :: "expr => constr => bool"
where [simp]: "satisfies e All"
    | [simp]: "satisfies e c1 ==> satisfies e c2 ==> satisfies e (And c1 c2)"
    | [simp]: "satisfies e c1 ==> satisfies e (Or c1 c2)"
    | [simp]: "satisfies e c2 ==> satisfies e (Or c1 c2)"
    | [simp]: "satisfies e c ==> satisfies (InL t1 t2 e) (CInL t1 t2 c)"
    | [simp]: "satisfies e c ==> satisfies (InR t1 t2 e) (CInR t1 t2 c)"
    | [simp]: "satisfies Triv CTriv"
    | [simp]: "satisfies e1 c1 ==> satisfies e2 c2 ==> satisfies (Pair e1 e2) (CPair c1 c2)"

inductive_cases [elim!]: "satisfies e All"
inductive_cases [elim!]: "satisfies e (And x y)"
inductive_cases [elim!]: "satisfies e Nothing"
inductive_cases [elim!]: "satisfies e (Or x y)"
inductive_cases [elim!]: "satisfies e (CInL x y z)"
inductive_cases [elim!]: "satisfies e (CInR x y z)"
inductive_cases [elim!]: "satisfies e CTriv"
inductive_cases [elim!]: "satisfies e (CPair x y)"

lemma [simp]: "satisfies e CTriv ==> e = Triv"
by (induction e CTriv rule: satisfies.induct, simp)

lemma [simp]: "satisfies e (CPair c1 c2) ==> EX e1 e2. e = Pair e1 e2"
by (induction e "CPair c1 c2" rule: satisfies.induct, simp)

lemma [simp]: "satisfies e (CInL t1 t2 c) ==> EX e'. e = InL t1 t2 e'"
by (induction e "CInL t1 t2 c" rule: satisfies.induct, simp)

lemma [simp]: "satisfies e (CInR t1 t2 c) ==> EX e'. e = InR t1 t2 e'"
by (induction e "CInR t1 t2 c" rule: satisfies.induct, simp)

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

primrec strip_inl :: "constr => constr"
where "strip_inl All = All"
    | "strip_inl (And c1 c2) = And (strip_inl c1) (strip_inl c2)"
    | "strip_inl Nothing = Nothing"
    | "strip_inl (Or c1 c2) = Or (strip_inl c1) (strip_inl c2)"
    | "strip_inl (CInL t1 t2 c) = c"
    | "strip_inl (CInR t1 t2 c) = Nothing"
    | "strip_inl CTriv = Nothing"
    | "strip_inl (CPair c1 c2) = Nothing"

primrec strip_inr :: "constr => constr"
where "strip_inr All = All"
    | "strip_inr (And c1 c2) = And (strip_inr c1) (strip_inr c2)"
    | "strip_inr Nothing = Nothing"
    | "strip_inr (Or c1 c2) = Or (strip_inr c1) (strip_inr c2)"
    | "strip_inr (CInL t1 t2 c) = Nothing"
    | "strip_inr (CInR t1 t2 c) = c"
    | "strip_inr CTriv = Nothing"
    | "strip_inr (CPair c1 c2) = Nothing"

primrec strip_pair_1 :: "constr => constr"
where "strip_pair_1 All = All"
    | "strip_pair_1 (And c1 c2) = And (strip_pair_1 c1) (strip_pair_1 c2)"
    | "strip_pair_1 Nothing = Nothing"
    | "strip_pair_1 (Or c1 c2) = Or (strip_pair_1 c1) (strip_pair_1 c2)"
    | "strip_pair_1 (CInL t1 t2 c) = Nothing"
    | "strip_pair_1 (CInR t1 t2 c) = Nothing"
    | "strip_pair_1 CTriv = Nothing"
    | "strip_pair_1 (CPair c1 c2) = c1"

primrec strip_pair_2 :: "constr => constr"
where "strip_pair_2 All = All"
    | "strip_pair_2 (And c1 c2) = And (strip_pair_2 c1) (strip_pair_2 c2)"
    | "strip_pair_2 Nothing = Nothing"
    | "strip_pair_2 (Or c1 c2) = Or (strip_pair_2 c1) (strip_pair_2 c2)"
    | "strip_pair_2 (CInL t1 t2 c) = Nothing"
    | "strip_pair_2 (CInR t1 t2 c) = Nothing"
    | "strip_pair_2 CTriv = Nothing"
    | "strip_pair_2 (CPair c1 c2) = c2"

inductive incon :: "constr list => bool"
where ical [simp]: "incon cs ==> incon (All # cs)"
    | ican [simp]: "incon (c1 # c2 # cs) ==> incon (And c1 c2 # cs)"
    | icno [simp]: "incon (Nothing # cs)"
    | icor [simp]: "incon (c1 # cs) ==> incon (c2 # cs) ==> incon (Or c1 c2 # cs)"
    | icil [simp]: "incon (map strip_inl cs) ==> incon (CInL t1 t2 c # cs)" 
    | icir [simp]: "incon (map strip_inr cs) ==> incon (CInR t1 t2 c # cs)" 
    | icp1 [simp]: "incon (c1 # map strip_pair_1 cs) ==> incon (CPair c1 c2 # cs)"
    | icp2 [simp]: "incon (c2 # map strip_pair_2 cs) ==> incon (CPair c1 c2 # cs)" 

inductive_cases [elim!]: "incon (All # cs)"
inductive_cases [elim!]: "incon (And x y # cs)"
inductive_cases [elim!]: "incon (Nothing # cs)"
inductive_cases [elim!]: "incon (Or x y # cs)"
inductive_cases [elim!]: "incon (CInL x y z # cs)"
inductive_cases [elim!]: "incon (CInR x y z # cs)"
inductive_cases [elim!]: "incon (CPair x y # cs)"

definition totally_satisfied :: "constr => bool"
where "totally_satisfied c = incon [de_morgan_dual c]"

lemma [simp]: "typecheck_constr c t ==> totally_satisfied c ==> typecheck env e t ==> is_val e ==> satisfies e c"
proof (simp add: totally_satisfied_def, induction c t arbitrary: env e rule: typecheck_constr.induct)
case tcal
  thus ?case by auto
next case tcan
  thus ?case by auto
next case tcno
  thus ?case by auto sorry
next case tcor
  thus ?case by auto sorry
next case tcil
  thus ?case by auto sorry
next case tcir
  thus ?case by auto sorry
next case tctr
  thus ?case apply auto by simp sorry
next case tcpr
  thus ?case by auto sorry
qed

lemma [simp]: "totally_satisfied (Or c cs) ==> is_val e ==> satisfies e cs ==> ~ satisfies e c"
by simp
sorry

inductive all_matches_complete :: "expr => bool"
      and extract_constraints :: "rule list => type => constr => bool"
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
    | [simp]: "all_matches_complete e ==> extract_constraints rs t c ==> totally_satisfied c ==> all_matches_complete (Match e t rs)"
    | [simp]: "extract_constraints [] t Nothing"
    | [simp]: "extract_constraint_rule r t c1 ==> extract_constraints rs t c2 ==> extract_constraints (r # rs) t (Or c1 c2)"
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

lemma [simp]: "types_from_pat p t ts ==> extract_constraint p t c ==> satisfies e c ==> EX s. matches s p e"
proof (induction p t ts arbitrary: e c rule: types_from_pat.induct)
case tpwld
  have "matches [] Wild e" by simp
  thus ?case by (rule exI)
next case tpvar
  have "matches [e] PVar e" by simp
  thus ?case by (rule exI)
next case tptrv
  hence "c = CTriv" by simp
  with tptrv have X: "e = Triv" by simp
  have "matches [] PTriv Triv" by simp
  hence "EX s. matches s PTriv Triv" by (rule exI)
  with X show ?case by simp
next case (tppar p1 t1 _ p2 t2 _)
  then obtain c1 c2 where "extract_constraint p1 t1 c1 & extract_constraint p2 t2 c2 & c = CPair c1 c2" by auto
  with tppar show ?case
  proof auto
    fix e1 e2
    assume "extract_constraint p1 t1 c1"
       and "!!cc ee. extract_constraint p1 t1 cc \<Longrightarrow> satisfies ee cc \<Longrightarrow> \<exists>s. matches s p1 ee"
       and "satisfies e1 c1" 
       and X: "extract_constraint p2 t2 c2"
       and Y: "!!cc ee. extract_constraint p2 t2 cc \<Longrightarrow> satisfies ee cc \<Longrightarrow> \<exists>s. matches s p2 ee"
       and Z: "satisfies e2 c2"
    hence "EX s. matches s p1 e1" by simp
    then obtain s1 where A: "matches s1 p1 e1" by auto
    from X Y Z have "EX s. matches s p2 e2" by simp
    then obtain s2 where "matches s2 p2 e2" by auto
    with A have "matches (s1 @ s2) (PPair p1 p2) (Pair e1 e2)" by simp 
    thus "EX s. matches s (PPair p1 p2) (Pair e1 e2)" by (rule exI)
  qed
next case (tpinl p t1 _ t2)
  then obtain c' where C: "extract_constraint p t1 c' & c = CInL t1 t2 c'" by auto
  with tpinl show ?case
  proof auto
    fix e'
    assume "!!cc ee. extract_constraint p t1 cc \<Longrightarrow> satisfies ee cc \<Longrightarrow> \<exists>s. matches s p ee"
       and "satisfies e' c'" 
    with C obtain s where "matches s p e'" by auto
    hence "matches s (PInL p) (InL t1 t2 e')" by simp
    thus "EX s. matches s (PInL p) (InL t1 t2 e')" by (rule exI)
  qed
next case (tpinr p t2 _ t1)
  hence "EX c'. extract_constraint p t2 c' & c = CInR t1 t2 c'" by auto
  with tpinr show ?case
  proof auto
    fix e' c'
    assume "extract_constraint p t2 c'"
       and "!!cc ee. extract_constraint p t2 cc \<Longrightarrow> satisfies ee cc \<Longrightarrow> \<exists>s. matches s p ee"
       and "satisfies e' c'" 
    hence "EX s. matches s p e'" by simp
    thus "EX s. matches s (PInR p) (InR t1 t2 e')"
    proof auto
      fix s
      assume "matches s p e'" 
      hence "matches s (PInR p) (InR t1 t2 e')" by simp
      thus "EX s. matches s (PInR p) (InR t1 t2 e')" by (rule exI)
    qed
  qed
qed

end
