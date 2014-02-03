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
    | "is_val (Match e rs) = False"

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
where [simp]: "matches [] Wild e"
    | [simp]: "matches [e] PVar e"
    | [simp]: "matches [] PTriv Triv"
    | [simp]: "matches s1 p1 e1 ==> matches s2 p2 e2 ==> matches (s1 @ s2) (PPair p1 p2) (Pair e1 e2)"
    | [simp]: "matches s p e ==> matches s (PInL p) (InL t t' e)"
    | [simp]: "matches s p e ==> matches s (PInR p) (InR t t' e)"

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
apply (induction s p e rule: matches.induct)
apply auto
sorry

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

end
