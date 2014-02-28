theory Chapter13_3_PatternMatching
imports Chapter13_2_Typechecking
begin

fun is_val :: "expr => bool"
where "is_val (Var v) = False"
    | "is_val Zero = True"
    | "is_val (Succ n) = is_val n"
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
    | "is_val (Case e t rs) = False"

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
where mtcht [simp]: "matches [] PTriv Triv"
    | mtchp [simp]: "matches [e1, e2] PPair (Pair e1 e2)"
    | mtchl [simp]: "matches [e] PInL (InL t t' e)"
    | mtchr [simp]: "matches [e] PInR (InR t t' e)"
    | mtchz [simp]: "matches [] PZero Zero"
    | mtchs [simp]: "matches [e] PSucc (Succ e)"

inductive_cases [elim!]: "matches s PTriv e"
inductive_cases [elim!]: "matches s PPair e"
inductive_cases [elim!]: "matches s PInL e"
inductive_cases [elim!]: "matches s PInR e"
inductive_cases [elim!]: "matches s PZero e"
inductive_cases [elim!]: "matches s PSucc e"

inductive no_match :: "expr => patn => bool"
where [simp]: "no_match (InL t t' e) PInR"
    | [simp]: "no_match (InR t t' e) PInL"
    | [simp]: "no_match Zero PSucc"
    | [simp]: "no_match (Succ e) PZero"

lemma [simp]: "(~ no_match e p) = matches s p e"
proof auto
  show "~ no_match e p ==> matches s p e" by simp sorry
next 
  show "matches s p e ==> no_match e p ==> False"
  proof (induction s p e rule: matches.induct)
  case mtcht
    thus ?case by (induction Triv PTriv rule: no_match.induct)
  next case (mtchp e1 e2)
    thus ?case by (induction "Pair e1 e2" PPair rule: no_match.induct)
  next case (mtchl e t t')
    thus ?case by (induction "InL t t' e" PInL rule: no_match.induct)
  next case (mtchr e t t')
    thus ?case by (induction "InR t t' e" PInR rule: no_match.induct)
  next case mtchz
    thus ?case by (induction Zero PZero rule: no_match.induct)
  next case (mtchs e)
    thus ?case by (induction "Succ e" PSucc rule: no_match.induct)
  qed
qed

lemma [simp]: "types_from_pat p t ts ==> typecheck env e t ==> is_val e ==> (EX s. typecheck_subst env s ts & matches s p e) | no_match e p"
proof (induction p t ts arbitrary: e rule: types_from_pat.induct)
case tptrv
  hence "e = Triv" by (simp add: canonical_unit)
  thus ?case by simp sorry
next case (tppar t1 t2)
  hence "(EX e1 e2. e = Pair e1 e2 & typecheck env e1 t1 & typecheck env e2 t2 & is_val e1 & is_val e2)" by (simp add: canonical_prod)
  with tppar show ?case by auto sorry
next case (tpinl t1 t2)
  from tpinl have "(EX e'. e = InL t1 t2 e' & is_val e' & typecheck env e' t1) | (EX e'. e = InR t1 t2 e' & is_val e' & typecheck env e' t2)" by (simp add: canonical_sum)
  with tpinl show ?case
  proof (cases "EX e'. e = InL t1 t2 e'", auto)
    fix e'
    show "EX s. typecheck_subst env s [t1] & matches s PInL (InL t1 t2 e')" by auto sorry
  qed
next case (tpinr t1 t2)
  from tpinr have "(EX e'. e = InL t1 t2 e' & is_val e' & typecheck env e' t1) | (EX e'. e = InR t1 t2 e' & is_val e' & typecheck env e' t2)" by (simp add: canonical_sum)
  with tpinr show ?case
  proof (cases "EX e'. e = InR t1 t2 e'", auto)
    fix e'
    assume "\<not> no_match (InR t1 t2 e') PInR" 
       and "is_val e'" 
       and "typecheck env e' t2"
    show "EX s. typecheck_subst env s [t2] & matches s PInR (InR t1 t2 e')" by auto sorry
  qed
next case tpzer
  hence "e = Zero | (EX v. typecheck env v Nat & is_val v & e = Succ v)" by (simp add: canonical_nat)
  thus ?case by simp sorry
next case tpsuc
  hence "e = Zero | (EX v. typecheck env v Nat & is_val v & e = Succ v)" by (simp add: canonical_nat)
  show ?case by auto sorry
qed

lemma [simp]: "matches s p e ==> matches s' p e ==> s = s'"
by (induction s p e arbitrary: s' rule: matches.induct, auto)

lemma [simp]: "matches s p e ==> typecheck env e t ==> types_from_pat p t ts ==> typecheck_subst env s ts"
by (induction s p e arbitrary: t ts rule: matches.induct, auto)

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

fun perfectly_satisfied :: "type => patn list => bool"
where "perfectly_satisfied t [] = False"
    | "perfectly_satisfied t (PInL # ps) = (ps = [PInR] & (EX t1 t2. t = Sum t1 t2))"
    | "perfectly_satisfied t (PInR # ps) = (ps = [PInL] & (EX t1 t2. t = Sum t1 t2))"
    | "perfectly_satisfied t (PTriv # cs) = (cs = [] & t = Unit)"
    | "perfectly_satisfied t (PPair # cs) = (cs = [] & (EX t1 t2. t = Prod t1 t2))"
    | "perfectly_satisfied t (PZero # cs) = (cs = [PSucc] & t = Nat)"
    | "perfectly_satisfied t (PSucc # cs) = (cs = [PZero] & t = Nat)"

inductive all_matches_complete :: "expr => bool"
      and extract_patterns :: "rule list => patn list => bool"
      and extract_pattern :: "rule => patn => bool"
where [simp]: "all_matches_complete (Var v)" 
    | [simp]: "all_matches_complete Zero"
    | [simp]: "all_matches_complete e ==> all_matches_complete (Succ e)"
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
    | [simp]: "all_matches_complete e ==> extract_patterns rs ps ==> perfectly_satisfied t ps ==> all_matches_complete (Case e t rs)"
    | [simp]: "extract_patterns [] []"
    | [simp]: "extract_pattern r p ==> extract_patterns rs ps ==> extract_patterns (r # rs) (p # ps)"
    | [simp]: "all_matches_complete e ==> extract_pattern (Rule p e) p"

inductive_cases [elim!]: "all_matches_complete (Var x)"
inductive_cases [elim!]: "all_matches_complete Zero"
inductive_cases [elim!]: "all_matches_complete (Succ x)"
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
inductive_cases [elim!]: "all_matches_complete (Case x y z)"
inductive_cases [elim!]: "extract_patterns [] c"
inductive_cases [elim!]: "extract_patterns (x # y) c"
inductive_cases [elim!]: "extract_pattern (Rule x y) c"

end
