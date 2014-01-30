theory Chapter11A
imports AssocList
begin

datatype type = Nat | Arr type type

datatype expr = 
  Var nat 
| Zero
| Succ expr
| IsZ expr expr expr
| Lam type expr
| Ap expr expr
| Fix type expr

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

primrec free_vars :: "expr => nat set"
where "free_vars (Var v) = {v}"
    | "free_vars Zero = {}"
    | "free_vars (Succ e) = free_vars e"
    | "free_vars (IsZ e0 e1 et) = free_vars e0 Un free_vars et Un redr_set (free_vars e1)"
    | "free_vars (Lam t b) = redr_set (free_vars b)"
    | "free_vars (Ap e1 e2) = free_vars e1 Un free_vars e2"
    | "free_vars (Fix t b) = redr_set (free_vars b)"

primrec incr_from :: "nat => expr => expr"
where "incr_from n (Var v) = Var (if v < n then v else Suc v)"
    | "incr_from n Zero = Zero"
    | "incr_from n (Succ e) = Succ (incr_from n e)"
    | "incr_from n (IsZ e0 e1 et) = IsZ (incr_from n e0) (incr_from (Suc n) e1) (incr_from n et)"
    | "incr_from n (Lam t b) = Lam t (incr_from (Suc n) b)"
    | "incr_from n (Ap e1 e2) = Ap (incr_from n e1) (incr_from n e2)"
    | "incr_from n (Fix t b) = Fix t (incr_from (Suc n) b)"

lemma [simp]: "free_vars (incr_from n e) = (%v. if v < n then v else Suc v) ` free_vars e"
proof (induction e arbitrary: n)
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
qed

primrec sub_from :: "nat => expr => expr"
where "sub_from n (Var v) = Var (if v < n then v else if v = n then undefined else v - 1)"
    | "sub_from n Zero = Zero"
    | "sub_from n (Succ e) = Succ (sub_from n e)"
    | "sub_from n (IsZ e0 e1 et) = IsZ (sub_from n e0) (sub_from (Suc n) e1) (sub_from n et)"
    | "sub_from n (Lam t b) = Lam t (sub_from (Suc n) b)"
    | "sub_from n (Ap e1 e2) = Ap (sub_from n e1) (sub_from n e2)"
    | "sub_from n (Fix t b) = Fix t (sub_from (Suc n) b)"

primrec subst :: "expr => expr => nat => expr"
where "subst (Var v) e x = (if v = x then e else Var v)"
    | "subst Zero e x = Zero"
    | "subst (Succ n) e x = Succ (subst n e x)"
    | "subst (IsZ e0 e1 et) e x = IsZ (subst e0 e x) (subst e1 (incr_from 0 e) (Suc x)) (subst et e x)"
    | "subst (Lam t b) e x = Lam t (subst b (incr_from 0 e) (Suc x))"
    | "subst (Ap e1 e2) e x = Ap (subst e1 e x) (subst e2 e x)"
    | "subst (Fix t b) e x = Fix t (subst b (incr_from 0 e) (Suc x))"

definition safe_subst :: "expr => expr => expr"
where "safe_subst e e' = sub_from 0 (subst e (incr_from 0 e') 0)"

lemma [simp]: "free_vars (subst e e' x) = (if x : free_vars e then free_vars e - {x} Un free_vars e' else free_vars e)"
by (induction e arbitrary: e' x, auto)

inductive typecheck :: "(nat, type) assoc => expr => type => bool"
where tvar [simp]: "lookup env v = Some t ==> typecheck env (Var v) t"
    | tzer [simp]: "typecheck env Zero Nat"    
    | tsuc [simp]: "typecheck env n Nat ==> typecheck env (Succ n) Nat"
    | trec [simp]: "typecheck env e Nat ==> typecheck env e0 t ==> 
                        typecheck (extend_at env 0 Nat) e1 t ==> 
                            typecheck env (IsZ e0 e1 e) t"
    | tlam [simp]: "typecheck (extend_at env 0 r) e t ==> typecheck env (Lam r e) (Arr r t)"
    | tapp [simp]: "typecheck env e1 (Arr t2 t) ==> typecheck env e2 t2 ==> 
                        typecheck env (Ap e1 e2) t"
    | tfix [simp]: "typecheck (extend_at env 0 t) b t ==> typecheck env (Fix t b) t"

inductive_cases [elim!]: "typecheck e (Var x) t"
inductive_cases [elim!]: "typecheck e Zero t"
inductive_cases [elim!]: "typecheck e (Succ x) t"
inductive_cases [elim!]: "typecheck e (IsZ x y z) t"
inductive_cases [elim!]: "typecheck e (Lam x y) t"
inductive_cases [elim!]: "typecheck e (Ap x y) t"
inductive_cases [elim!]: "typecheck e (Fix x y) t"

lemma inv_var: "typecheck env (Var v) t ==> lookup env v = Some t" 
by auto
lemma inv_zer: "typecheck env Zero t ==> t = Nat" 
by auto
lemma inv_suc: "typecheck env (Succ n) t ==> t = Nat & typecheck env n Nat"
by auto
lemma inv_rec: "typecheck env (IsZ e0 e1 e) t ==> typecheck env e Nat & typecheck env e0 t & typecheck (extend_at env 0 Nat) e1 t"
by auto
lemma inv_lam: "typecheck env (Lam r e) t ==> EX t'. t = Arr r t' & typecheck (extend_at env 0 r) e t'"
by auto
lemma inv_app: "typecheck env (Ap e1 e2) t ==> EX t2. typecheck env e1 (Arr t2 t) & typecheck env e2 t2"
by auto
lemma inv_fix: "typecheck env (Fix r b) t ==> t = r & typecheck (extend_at env 0 t) b t"
by auto
                        
lemma [simp]: "typecheck env e t ==> typecheck (extend_at env n k) (incr_from n e) t"
proof (induction env e t arbitrary: n rule: typecheck.induct)
case tvar
  thus ?case by simp
next case tzer
  thus ?case by simp
next case tsuc
  thus ?case by simp
next case (trec env e e0 t e1)
  hence "typecheck (extend_at (extend_at env 0 Nat) (Suc n) k) (incr_from (Suc n) e1) t" by simp
  with trec show ?case by (simp add: extend_at_swap)
next case (tlam env r b t)
  hence "typecheck (extend_at (extend_at env 0 r) (Suc n) k) (incr_from (Suc n) b) t" by simp
  thus ?case by (simp add: extend_at_swap)
next case (tapp env e1 t2 t e2)
  from tapp have "typecheck (extend_at env n k) (incr_from n e1) (Arr t2 t)" by simp
  moreover from tapp have "typecheck (extend_at env n k) (incr_from n e2) t2" by simp
  ultimately show ?case by simp
next case (tfix env t b)
  hence "typecheck (extend_at (extend_at env 0 t) (Suc n) k) (incr_from (Suc n) b) t" by simp
  thus ?case by (simp add: extend_at_swap)
qed

lemma [simp]: "typecheck (extend_at env n k) e t ==> n ~: free_vars e ==> typecheck env (sub_from n e) t"
proof (induction "extend_at env n k" e t arbitrary: env n rule: typecheck.induct)
case (tvar v t)
  thus ?case by (cases "v < n", simp, cases "v = n", simp_all)
next case tzer
  thus ?case by simp
next case tsuc
  thus ?case by simp
next case (trec e e0 t e1)
  moreover hence "Suc n ~: free_vars e1" by auto
  moreover have "extend_at (extend_at env n k) 0 Nat = extend_at (extend_at env 0 Nat) (Suc n) k" by (simp add: extend_at_swap)
  ultimately show ?case by simp
next case tlam
  thus ?case by (simp add: extend_at_swap)
next case (tapp e1 t2 t e2)
  from tapp have "typecheck env (sub_from n e1) (Arr t2 t)" by simp
  moreover from tapp have "typecheck env (sub_from n e2) t2" by simp
  ultimately show ?case by simp
next case tfix
  thus ?case by (simp add: extend_at_swap)
qed

lemma [simp]: "typecheck (extend env x t') e t ==> typecheck env e' t' ==> typecheck env (subst e e' x) t"
proof (induction "extend env x t'" e t arbitrary: env e' x rule: typecheck.induct)
case tvar
  thus ?case by auto
next case tzer
  thus ?case by simp
next case tsuc
  thus ?case by simp
next case trec
  thus ?case by simp
next case tlam
  thus ?case by simp
next case (tapp e1 t2 t e2)
  from tapp have "typecheck env (subst e1 e' x) (Arr t2 t)" by simp
  moreover from tapp have "typecheck env (subst e2 e' x) t2" by simp
  ultimately show ?case by simp
next case tfix
  thus ?case by simp
qed 

lemma [simp]: "typecheck (extend_at env 0 t') e t ==> typecheck env e' t' ==> typecheck env (safe_subst e e') t"
proof (simp add: safe_subst_def)
  assume "typecheck (extend_at env 0 t') e t"
     and "typecheck env e' t'"
  moreover have "0 ~: (if 0 : free_vars e then free_vars e - {0} Un free_vars (incr_from 0 e') else free_vars e)" by (cases "0 : free_vars e", auto)
  ultimately show "typecheck env (sub_from 0 (subst e (incr_from 0 e') 0)) t" by simp
qed

primrec is_val :: "expr => bool"
where "is_val (Var v) = False"
    | "is_val Zero = True"
    | "is_val (Succ n) = is_val n"
    | "is_val (IsZ e0 e1 et) = False"
    | "is_val (Lam t b) = True"
    | "is_val (Ap e1 e2) = False"
    | "is_val (Fix t b) = False"

inductive eval :: "expr => expr => bool"
where esuc [simp]: "eval n n' ==> eval (Succ n) (Succ n')"
    | eap1 [simp]: "eval e1 e1' ==> eval (Ap e1 e2) (Ap e1' e2)"
    | eap2 [simp]: "is_val e1 ==> eval e2 e2' ==> eval (Ap e1 e2) (Ap e1 e2')"
    | eap3 [simp]: "is_val e2 ==> eval (Ap (Lam t b) e2) (safe_subst b e2)"
    | eiz1 [simp]: "eval e e' ==> eval (IsZ e0 e1 e) (IsZ e0 e1 e')"
    | eiz2 [simp]: "eval (IsZ e0 e1 Zero) e0"
    | eiz3 [simp]: "is_val e ==> eval (IsZ e0 e1 (Succ e)) (safe_subst e1 e)"
    | efix [simp]: "eval (Fix t b) (safe_subst b (Fix t b))"

lemma canonical_nat: "typecheck env e Nat ==> is_val e ==> e = Zero | (EX v. typecheck env v Nat & is_val v & e = Succ v)"
by (induction e, auto)

lemma tc_can_nat: "typecheck env e Nat ==> is_val e ==> typecheck env' e Nat"
proof -
  assume "typecheck env e Nat"
     and "is_val e"
  hence "e = Zero | (EX v. typecheck env v Nat & is_val v & e = Succ v)" by (simp add: canonical_nat)
  thus "typecheck env' e Nat" by (induction e, simp_all add: canonical_nat)
qed

lemma canonical_arr: "typecheck env e (Arr t1 t2) ==> is_val e ==> (EX v. e = Lam t1 v & typecheck (extend_at env 0 t1) v t2)"
by (induction e, auto)

theorem preservation: "eval e e' ==> typecheck env e t ==> typecheck env e' t"
proof (induction e e' arbitrary: t env rule: eval.induct)
case esuc
  thus ?case by auto
next case (eap1 e1 e1' e2)
  hence "EX t2. typecheck env e1' (Arr t2 t) & typecheck env e2 t2" by auto
  thus ?case by auto
next case eap2
  thus ?case by auto
next case eap3
  thus ?case by auto
next case eiz1
  thus ?case by auto
next case eiz2
  thus ?case by auto
next case eiz3
  thus ?case by auto
next case efix
  thus ?case by auto
qed

theorem progress: "typecheck env e t ==> env = empty_map ==> is_val e | (EX e'. eval e e')"
proof (induct rule: typecheck.induct)
case tvar
  thus ?case by auto
next case tzer
  thus ?case by simp
next case (tsuc env n)
  thus ?case 
  proof (cases "is_val n", auto)
    fix x
    assume "eval n x"
    hence "eval (Succ n) (Succ x)" by simp
    thus "EX y. eval (Succ n) y " by auto
  qed
next case (trec env e e0 t e1)
  thus ?case
  proof (cases "is_val e")
  case True
    have "EX x. eval (IsZ e0 e1 e) x"
    proof (cases "e = Zero")
    case True
      def e0' == e0
      have "eval (IsZ e0 e1 Zero) e0'" by (simp add: e0'_def)
      with True show ?thesis by auto
    next case False
      from trec True have "e = Zero | (EX v. typecheck env v Nat & is_val v & e = Succ v)" by (simp add: canonical_nat)
      with False have "EX v. typecheck env v Nat & is_val v & e = Succ v" by simp
      thus ?thesis
      proof auto
        fix v
        assume "is_val v"
        hence "eval (IsZ e0 e1 (Succ v)) (safe_subst e1 v)" by simp
        thus "EX x. eval (IsZ e0 e1 (Succ v)) x" by auto
      qed
    qed
    thus ?thesis by simp
  next case False
    with trec have "\<exists>a. eval e a" by simp
    thus ?thesis
    proof auto
      fix a
      assume "eval e a"
      hence "eval (IsZ e0 e1 e) (IsZ e0 e1 a)" by simp
      thus "EX x. eval (IsZ e0 e1 e) x" by auto
    qed
  qed
next case tlam
  thus ?case by simp
next case (tapp env e1 t2 t e2)
  from tapp have "typecheck env e1 (Arr t2 t)" by simp
  from tapp have "typecheck env e2 t2" by simp
  from tapp have "is_val e2 \<or> (\<exists>a. eval e2 a)" by simp
  thus ?case
  proof (cases "is_val e1")
  case True
    with tapp have "EX v. e1 = Lam t2 v & typecheck (extend_at env 0 t2) v t" by (simp add: canonical_arr)
    hence e1_is_lam: "EX v. e1 = Lam t2 v" by auto
    thus ?thesis 
    proof (cases "is_val e2")
    case True
      with e1_is_lam show ?thesis
      proof auto
        fix v
        assume "is_val e2"
        hence "eval (Ap (Lam t2 v) e2) (safe_subst v e2)" by simp
        thus "EX x. eval (Ap (Lam t2 v) e2) x" by auto
      qed
    next case False
      with tapp have "\<exists>a. eval e2 a" by simp
      thus ?thesis
      proof auto
        fix a
        assume "eval e2 a"
        moreover from True have "is_val e1" by simp
        ultimately have "eval (Ap e1 e2) (Ap e1 a)" by simp
        thus "EX x. eval (Ap e1 e2) x" by auto
      qed
    qed
  next case False
    with tapp have "\<exists>a. eval e1 a" by simp
    thus ?thesis
    proof auto
      fix a
      assume "eval e1 a"
      hence "eval (Ap e1 e2) (Ap a e2)" by simp
      thus "EX x. eval (Ap e1 e2) x" by auto
    qed
  qed
next case (tfix env t b)
  def b' == "safe_subst b (Fix t b)"
  have "eval (Fix t b) b'" by (simp add: b'_def)
  thus ?case by auto
qed 

end
