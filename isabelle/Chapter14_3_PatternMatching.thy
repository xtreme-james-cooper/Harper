theory Chapter14_3_PatternMatching
imports Chapter14_2_Typechecking
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
    | "is_val (Map t e e') = False"

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

fun matches :: "patn => expr => expr list option"
where "matches PTriv Triv = Some []"
    | "matches PTriv e = None"
    | "matches PPair (Pair e1 e2) = Some [e1, e2]"
    | "matches PPair e = None"
    | "matches PInL (InL t t' e) = Some [e]"
    | "matches PInL e = None"
    | "matches PInR (InR t t' e) = Some [e]"
    | "matches PInR e = None"
    | "matches PZero Zero = Some []"
    | "matches PZero e = None"
    | "matches PSucc (Succ e) = Some [e]"
    | "matches PSucc e = None"

lemma [simp]: "types_from_pat p t ts ==> typecheck env e t ==> is_val e ==> matches p e = Some s ==> typecheck_subst env s ts"
proof (induction p t ts rule: types_from_pat.induct)
case tptrv
  hence "e = Triv" by (simp add: canonical_unit)
  with tptrv show ?case by simp
next case (tppar t1 t2)
  hence "EX e1 e2. e = Pair e1 e2 & typecheck env e1 t1 & typecheck env e2 t2 & is_val e1 & is_val e2" by (simp add: canonical_prod)
  then obtain e1 e2 where "e = Pair e1 e2 & typecheck env e1 t1 & typecheck env e2 t2 & is_val e1 & is_val e2" by auto
  with tppar show ?case by auto
next case (tpinl t1 t2)
  hence "(EX e'. e = InL t1 t2 e' & is_val e' & typecheck env e' t1) | (EX e'. e = InR t1 t2 e' & is_val e' & typecheck env e' t2)" by (simp add: canonical_sum)
  with tpinl show ?case by (cases "EX e'. e = InR t1 t2 e' & is_val e' & typecheck env e' t2", auto)
next case (tpinr t1 t2)
  hence "(EX e'. e = InL t1 t2 e' & is_val e' & typecheck env e' t1) | (EX e'. e = InR t1 t2 e' & is_val e' & typecheck env e' t2)" by (simp add: canonical_sum)
  with tpinr show ?case by (cases "EX e'. e = InL t1 t2 e' & is_val e' & typecheck env e' t1", auto)
next case tpzer
  hence "e = Zero | (EX v. typecheck env v Nat & is_val v & e = Succ v)" by (simp add: canonical_nat)
  with tpzer show ?case by auto
next case tpsuc
  hence "e = Zero | (EX v. typecheck env v Nat & is_val v & e = Succ v)" by (simp add: canonical_nat)
  with tpsuc show ?case by auto
qed

lemma [simp]: "matches p e = Some s ==> typecheck env e t ==> types_from_pat p t ts ==> typecheck_subst env s ts"
by (induction p e arbitrary: t ts rule: matches.induct, auto)

lemma [simp]: "matches p e = Some s ==> typecheck (extend_env ts env) e2 t ==> typecheck_subst env s ts ==> typecheck env (apply_subst s e2) t"
by auto

primrec perfectly_satisfied :: "type => patn list => bool"
where "perfectly_satisfied (Sum t1 t2) ps = (ps = [PInL, PInR] | ps = [PInR, PInL])"
    | "perfectly_satisfied Unit ps = (ps = [PTriv])"
    | "perfectly_satisfied (Prod t1 t2) ps = (ps = [PPair])"
    | "perfectly_satisfied Nat ps = (ps = [PZero, PSucc] | ps = [PSucc, PZero])"
    | "perfectly_satisfied Void ps = False"
    | "perfectly_satisfied (Arr t1 t2) ps = False"
    | "perfectly_satisfied (TyVar x) ps = False"

lemma [simp]: "~ perfectly_satisfied t []"
by (induction t, simp_all)

definition extract_patterns :: "rule list => patn list"
where [simp]: "extract_patterns = map (%r. case r of Rule p _ => p)"

inductive all_matches_complete :: "expr => bool"
      and check_rules :: "rule list => bool"
      and check_rule :: "rule => bool"
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
    | [simp]: "all_matches_complete e ==> check_rules rs ==> perfectly_satisfied t (extract_patterns rs) ==> 
                all_matches_complete (Case e t rs)"
    | [simp]: "check_rules []"
    | [simp]: "check_rule r ==> check_rules rs ==> check_rules (r # rs)"
    | [simp]: "all_matches_complete e ==> check_rule (Rule p e)"

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
inductive_cases [elim!]: "check_rules []"
inductive_cases [elim!]: "check_rules (x # y)"
inductive_cases [elim!]: "check_rule (Rule x y)"

end
