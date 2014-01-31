theory Chapter13_1_Language
imports AssocList
begin

datatype type = 
  Nat 
| Arr type type 
| Unit 
| Prod type type 
| Void 
| Sum type type

datatype patn =
  Wild
| Var
| PTriv
| PPair patn patn
| PInL patn
| PInR patn

primrec vars_count :: "patn => nat"
where "vars_count Wild = 0"
    | "vars_count Var = 1"
    | "vars_count PTriv = 0"
    | "vars_count (PPair p1 p2) = vars_count p1 + vars_count p2"
    | "vars_count (PInL p) = vars_count p"
    | "vars_count (PInR p) = vars_count p"

datatype expr = 
  Var nat 
| Zero
| Succ expr
| IsZ expr expr expr
| Lam type expr
| Ap expr expr
| Fix type expr
| Triv
| Pair expr expr
| ProjL expr
| ProjR expr
| Abort type expr
| InL type type expr
| InR type type expr
| Match expr "rule list"
and rule = Rule patn expr

definition redr_set :: "nat set => nat set"
where "redr_set xs = (%n. case n of 0 => undefined | Suc n => n) ` (xs - {0})"

lemma [simp]: "(n : redr_set xs) = (Suc n : xs)" 
proof (auto simp add: redr_set_def)
  fix x
  assume "x : xs"
     and "Suc (case x of Suc n => n) ~: xs"
  thus "x = 0" by (cases x, simp_all)
next
  assume "Suc n : xs"
  hence "n = (case Suc n of Suc n => n) ==> n : (%x. case x of Suc n => n)`(xs - {0})" by blast
  thus "n : (%x. case x of Suc n => n) ` (xs - {0})" by simp
qed

primrec redr_set_by :: "nat => nat set => nat set"
where "redr_set_by 0 xs = xs"
    | "redr_set_by (Suc n) xs = redr_set_by n (redr_set xs)"

lemma [simp]: "(x : redr_set_by n xs) = (x + n : xs)" 
by (induction n arbitrary: xs, simp_all)

primrec free_vars :: "expr => nat set"
    and free_vars_rules :: "rule list => nat set"
    and free_vars_rule :: "rule => nat set"
where "free_vars (Var v) = {v}"
    | "free_vars Zero = {}"
    | "free_vars (Succ e) = free_vars e"
    | "free_vars (IsZ e0 e1 et) = free_vars e0 Un free_vars et Un redr_set (free_vars e1)"
    | "free_vars (Lam t b) = redr_set (free_vars b)"
    | "free_vars (Ap e1 e2) = free_vars e1 Un free_vars e2"
    | "free_vars (Fix t b) = redr_set (free_vars b)"
    | "free_vars Triv = {}"
    | "free_vars (Pair e1 e2) = free_vars e1 Un free_vars e2"
    | "free_vars (ProjL e) = free_vars e"
    | "free_vars (ProjR e) = free_vars e"
    | "free_vars (Abort t e) = free_vars e"
    | "free_vars (InL t t' e) = free_vars e"
    | "free_vars (InR t t' e) = free_vars e"
    | "free_vars (Match e rs) = free_vars e Un free_vars_rules rs"
    | "free_vars_rules Nil = {}"
    | "free_vars_rules (r # rs) = free_vars_rule r Un free_vars_rules rs"    
    | "free_vars_rule (Rule p e) = redr_set_by (vars_count p) (free_vars e)"

primrec incr_from :: "nat => expr => expr"
    and incr_from_rules :: "nat => rule list => rule list"
    and incr_from_rule :: "nat => rule => rule"
where "incr_from n (Var v) = Var (if v < n then v else Suc v)"
    | "incr_from n Zero = Zero"
    | "incr_from n (Succ e) = Succ (incr_from n e)"
    | "incr_from n (IsZ e0 e1 et) = IsZ (incr_from n e0) (incr_from (Suc n) e1) (incr_from n et)"
    | "incr_from n (Lam t b) = Lam t (incr_from (Suc n) b)"
    | "incr_from n (Ap e1 e2) = Ap (incr_from n e1) (incr_from n e2)"
    | "incr_from n (Fix t b) = Fix t (incr_from (Suc n) b)"
    | "incr_from n Triv = Triv"
    | "incr_from n (Pair e1 e2) = Pair (incr_from n e1) (incr_from n e2)"
    | "incr_from n (ProjL e) = ProjL (incr_from n e)"
    | "incr_from n (ProjR e) = ProjR (incr_from n e)"
    | "incr_from n (Abort t e) = Abort t (incr_from n e)"
    | "incr_from n (InL t t' e) = InL t t' (incr_from n e)"
    | "incr_from n (InR t t' e) = InR t t' (incr_from n e)"
    | "incr_from n (Match e rs) = Match (incr_from n e) (incr_from_rules n rs)"
    | "incr_from_rules n Nil = Nil"
    | "incr_from_rules n (r # rs) = incr_from_rule n r # incr_from_rules n rs"    
    | "incr_from_rule n (Rule p e) = Rule p (incr_from (n + vars_count p) e)"

lemma [simp]: "free_vars (incr_from n e) = (%v. if v < n then v else Suc v) ` free_vars e"
  and [simp]: "free_vars_rules (incr_from_rules n rs) = (%v. if v < n then v else Suc v) ` free_vars_rules rs"
  and [simp]: "free_vars_rule (incr_from_rule n r) = (%v. if v < n then v else Suc v) ` free_vars_rule r"
proof (induction e and rs and r arbitrary: n)
case Var
  thus ?case by simp
next case Zero
  thus ?case by simp
next case Succ
  thus ?case by simp
next case (IsZ e0 e1 e)
  thus ?case
  proof auto
    fix xa
    show "xa ~: Suc ` ((free_vars e0 Un free_vars e Un redr_set (free_vars e1)) Int {v. ~ v < n}) ==> xa : free_vars e1 ==> ~ xa < Suc n ==> xa : free_vars e0" by (cases xa, auto)
  next
    fix xa
    show "xa ~: Suc ` ((free_vars e0 Un free_vars e Un redr_set (free_vars e1)) Int {v. ~ v < n}) ==> xa : free_vars e1 ==> ~ xa < Suc n ==> False" by (cases xa, auto)
  qed
next case (Lam t b)
  thus ?case
  proof auto
    fix xa
    show "xa ~: Suc ` (redr_set (free_vars b) Int {v. ~ v < n}) ==> xa : free_vars b ==> ~ xa < Suc n ==> Suc xa : free_vars b" by (cases xa, simp_all)
  next
    fix xa
    show "xa ~: Suc ` (redr_set (free_vars b) Int {v. ~ v < n}) ==> xa : free_vars b ==> ~ xa < Suc n ==> False" by (cases xa, simp_all)
  qed
next case Ap
  thus ?case by auto
next case (Fix t b)
  thus ?case
  proof auto
    fix xa
    show "xa ~: Suc ` (redr_set (free_vars b) Int {v. ~ v < n}) ==> xa : free_vars b ==> ~ xa < Suc n ==> Suc xa : free_vars b" by (cases xa, simp_all)
  next
    fix xa
    show "xa ~: Suc ` (redr_set (free_vars b) Int {v. ~ v < n}) ==> xa : free_vars b ==> ~ xa < Suc n ==> False" by (cases xa, simp_all)
  qed
next case Triv
  thus ?case by simp
next case Pair
  thus ?case by auto
next case ProjL
  thus ?case by simp
next case ProjR
  thus ?case by simp
next case Abort
  thus ?case by simp
next case InL
  thus ?case by simp
next case InR
  thus ?case by simp
next case (Match e rs)
  thus ?case by simp sorry
next case Nil_rule
  thus ?case by simp
next case Cons_rule
  thus ?case by simp sorry
next case Rule
  thus ?case by simp sorry
qed

primrec sub_from :: "nat => expr => expr"
    and sub_from_rules :: "nat => rule list => rule list"
    and sub_from_rule :: "nat => rule => rule"
where "sub_from n (Var v) = Var (if v < n then v else if v = n then undefined else v - 1)"
    | "sub_from n Zero = Zero"
    | "sub_from n (Succ e) = Succ (sub_from n e)"
    | "sub_from n (IsZ e0 e1 et) = IsZ (sub_from n e0) (sub_from (Suc n) e1) (sub_from n et)"
    | "sub_from n (Lam t b) = Lam t (sub_from (Suc n) b)"
    | "sub_from n (Ap e1 e2) = Ap (sub_from n e1) (sub_from n e2)"
    | "sub_from n (Fix t b) = Fix t (sub_from (Suc n) b)"
    | "sub_from n Triv = Triv"
    | "sub_from n (Pair e1 e2) = Pair (sub_from n e1) (sub_from n e2)"
    | "sub_from n (ProjL e) = ProjL (sub_from n e)"
    | "sub_from n (ProjR e) = ProjR (sub_from n e)"
    | "sub_from n (Abort t e) = Abort t (sub_from n e)"
    | "sub_from n (InL t t' e) = InL t t' (sub_from n e)"
    | "sub_from n (InR t t' e) = InR t t' (sub_from n e)"
    | "sub_from n (Match e rs) = Match (sub_from n e) (sub_from_rules n rs)"
    | "sub_from_rules n Nil = Nil"
    | "sub_from_rules n (r # rs) = sub_from_rule n r # sub_from_rules n rs"    
    | "sub_from_rule n (Rule p e) = Rule p (sub_from (n + vars_count p) e)"

primrec subst :: "expr => expr => nat => expr"
    and subst_rules :: "rule list => expr => nat => rule list"
    and subst_rule :: "rule => expr => nat => rule"
where "subst (Var v) e x = (if v = x then e else Var v)"
    | "subst Zero e x = Zero"
    | "subst (Succ n) e x = Succ (subst n e x)"
    | "subst (IsZ e0 e1 et) e x = IsZ (subst e0 e x) (subst e1 (incr_from 0 e) (Suc x)) (subst et e x)"
    | "subst (Lam t b) e x = Lam t (subst b (incr_from 0 e) (Suc x))"
    | "subst (Ap e1 e2) e x = Ap (subst e1 e x) (subst e2 e x)"
    | "subst (Fix t b) e x = Fix t (subst b (incr_from 0 e) (Suc x))"
    | "subst Triv e x = Triv"
    | "subst (Pair e1 e2) e x = Pair (subst e1 e x) (subst e2 e x)"
    | "subst (ProjL n) e x = ProjL (subst n e x)"
    | "subst (ProjR n) e x = ProjR (subst n e x)"
    | "subst (Abort t n) e x = Abort t (subst n e x)"
    | "subst (InL t t' n) e x = InL t t' (subst n e x)"
    | "subst (InR t t' n) e x = InR t t' (subst n e x)"
    | "subst (Match ec rs) e x = Match (subst ec e x) (subst_rules rs e x)"
    | "subst_rules Nil e x = Nil"
    | "subst_rules (r # rs) e x = subst_rule r e x # subst_rules rs e x"
    | "subst_rule (Rule p b) e x = Rule p (subst b (incr_from 0 e) (x + vars_count p))"

definition safe_subst :: "expr => expr => expr"
where "safe_subst e e' = sub_from 0 (subst e (incr_from 0 e') 0)"

lemma [simp]: "free_vars (subst e e' x) = (if x : free_vars e then free_vars e - {x} Un free_vars e' else free_vars e)"
  and [simp]: "free_vars_rules (subst_rules rs e' x) = (if x : free_vars_rules rs then free_vars_rules rs - {x} Un free_vars e' else free_vars_rules rs)"
  and [simp]: "free_vars_rule (subst_rule r e' x) = (if x : free_vars_rule r then free_vars_rule r - {x} Un free_vars e' else free_vars_rule r)"
proof (induction e and rs and r arbitrary: e' x)
case Var
  thus ?case by simp
next case Zero
  thus ?case by simp
next case Succ
  thus ?case by simp
next case IsZ
  thus ?case by auto
next case Lam
  thus ?case by auto
next case Ap
  thus ?case by auto
next case Fix
  thus ?case by auto
next case Triv
  thus ?case by simp
next case Pair
  thus ?case by auto
next case ProjL
  thus ?case by simp
next case ProjR
  thus ?case by simp
next case Abort
  thus ?case by simp
next case InL
  thus ?case by simp
next case InR
  thus ?case by simp
next case (Match e rs)
  thus ?case by auto sorry
next case Nil_rule
  thus ?case by simp
next case Cons_rule
  thus ?case by auto
next case Rule
  thus ?case by auto sorry
qed

end
