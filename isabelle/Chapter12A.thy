theory Chapter12A
imports AssocList
begin

datatype type = Nat | Arr type type | Unit | Prod type type | Void | Sum type type

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
| Case expr expr expr

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
    | "free_vars Triv = {}"
    | "free_vars (Pair e1 e2) = free_vars e1 Un free_vars e2"
    | "free_vars (ProjL e) = free_vars e"
    | "free_vars (ProjR e) = free_vars e"
    | "free_vars (Abort t e) = free_vars e"
    | "free_vars (InL t t' e) = free_vars e"
    | "free_vars (InR t t' e) = free_vars e"
    | "free_vars (Case e el er) = free_vars e Un redr_set (free_vars el) Un redr_set (free_vars er)"

primrec incr_from :: "nat => expr => expr"
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
    | "incr_from n (Case e el er) = Case (incr_from n e) (incr_from (Suc n) el) (incr_from (Suc n) er)"

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
next case (Case e el er)
  thus ?case
  proof auto
    fix xa
    show "xa ~: Suc ` ((free_vars e Un redr_set (free_vars el) Un redr_set (free_vars er)) Int {v. ~ v < n}) ==> 
            xa : free_vars el ==> ~ xa < Suc n ==> xa : free_vars e" by (cases xa, simp_all)
  next
    fix xa
    show "xa ~: Suc ` ((free_vars e Un redr_set (free_vars el) Un redr_set (free_vars er)) Int {v. ~ v < n}) ==> xa : free_vars el ==> ~ xa < Suc n ==> False" by (cases xa, simp_all)
  next
    fix xa
    show "xa ~: Suc ` ((free_vars e Un redr_set (free_vars el) Un redr_set (free_vars er)) Int {v. ~ v < n}) ==> xa : free_vars er ==> ~ xa < Suc n ==> xa : free_vars e" by (cases xa, simp_all)
  next
    fix xa
    show "xa ~: Suc ` ((free_vars e Un redr_set (free_vars el) Un redr_set (free_vars er)) Int {v. ~ v < n}) ==> xa : free_vars er ==> ~ xa < Suc n ==> False" by (cases xa, simp_all)
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
    | "sub_from n Triv = Triv"
    | "sub_from n (Pair e1 e2) = Pair (sub_from n e1) (sub_from n e2)"
    | "sub_from n (ProjL e) = ProjL (sub_from n e)"
    | "sub_from n (ProjR e) = ProjR (sub_from n e)"
    | "sub_from n (Abort t e) = Abort t (sub_from n e)"
    | "sub_from n (InL t t' e) = InL t t' (sub_from n e)"
    | "sub_from n (InR t t' e) = InR t t' (sub_from n e)"
    | "sub_from n (Case e el er) = Case (sub_from n e) (sub_from (Suc n) el) (sub_from (Suc n) er)"

primrec subst :: "expr => expr => nat => expr"
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
    | "subst (Case n el er) e x = Case (subst n e x) (subst el (incr_from 0 e) (Suc x)) (subst er (incr_from 0 e) (Suc x))"

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
    | ttrv [simp]: "typecheck env Triv Unit"
    | tpar [simp]: "typecheck env e1 t1 ==> typecheck env e2 t2 ==> typecheck env (Pair e1 e2) (Prod t1 t2)"
    | tprl [simp]: "typecheck env e (Prod t1 t2) ==> typecheck env (ProjL e) t1"
    | tprr [simp]: "typecheck env e (Prod t1 t2) ==> typecheck env (ProjR e) t2"
    | tabt [simp]: "typecheck env e Void ==> typecheck env (Abort t e) t"
    | tinl [simp]: "typecheck env e t1 ==> typecheck env (InL t1 t2 e) (Sum t1 t2)"
    | tinr [simp]: "typecheck env e t2 ==> typecheck env (InR t1 t2 e) (Sum t1 t2)"
    | tcse [simp]: "typecheck env e (Sum t1 t2) ==> typecheck (extend_at env 0 t1) el t ==> 
                        typecheck (extend_at env 0 t2) er t ==> typecheck env (Case e el er) t"

inductive_cases [elim!]: "typecheck e (Var x) t"
inductive_cases [elim!]: "typecheck e Zero t"
inductive_cases [elim!]: "typecheck e (Succ x) t"
inductive_cases [elim!]: "typecheck e (IsZ x y z) t"
inductive_cases [elim!]: "typecheck e (Lam x y) t"
inductive_cases [elim!]: "typecheck e (Ap x y) t"
inductive_cases [elim!]: "typecheck e (Fix x y) t"
inductive_cases [elim!]: "typecheck e Triv t"
inductive_cases [elim!]: "typecheck e (Pair x y) t"
inductive_cases [elim!]: "typecheck e (ProjL x) t"
inductive_cases [elim!]: "typecheck e (ProjR x) t"
inductive_cases [elim!]: "typecheck e (Abort x y) t"
inductive_cases [elim!]: "typecheck e (InL x y z) t"
inductive_cases [elim!]: "typecheck e (InR x y z) t"
inductive_cases [elim!]: "typecheck e (Case x y z) t"

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
lemma inv_tri: "typecheck env Triv t ==> t = Unit" 
by auto
lemma inv_par: "typecheck env (Pair e1 e2) t ==> (EX t1 t2. typecheck env e1 t1 & typecheck env e2 t2 & t = Prod t1 t2)"
by auto
lemma inv_prl: "typecheck env (ProjL e) t ==> (EX t2. typecheck env e (Prod t t2))"
by auto
lemma inv_prr: "typecheck env (ProjR e) t ==> (EX t1. typecheck env e (Prod t1 t))"
by auto
lemma inv_abt: "typecheck env (Abort r e) t ==> t = r & typecheck env e Void"
by auto
lemma inv_inl: "typecheck env (InL t1 t2 e) t ==> t = Sum t1 t2 & typecheck env e t1"
by auto
lemma inv_inr: "typecheck env (InR t1 t2 e) t ==> t = Sum t1 t2 & typecheck env e t2"
by auto
lemma inv_cse: "typecheck env (Case e el er) t ==> (EX t1 t2. typecheck env e (Sum t1 t2) & typecheck (extend_at env 0 t1) el t & typecheck (extend_at env 0 t2) er t)"
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
next case ttrv
  thus ?case by simp
next case tpar
  thus ?case by simp
next case (tprl env e t1 t2)
  hence "typecheck (extend_at env n k) (incr_from n e) (Prod t1 t2)" by simp
  thus ?case by simp 
next case (tprr env e t1 t2)
  hence "typecheck (extend_at env n k) (incr_from n e) (Prod t1 t2)" by simp
  thus ?case by simp
next case tabt
  thus ?case by simp
next case tinl
  thus ?case by simp
next case tinr
  thus ?case by simp
next case (tcse env e t1 t2 el t er)
  hence "typecheck (extend_at env n k) (incr_from n e) (Sum t1 t2)" by simp 
  moreover from tcse have "typecheck (extend_at (extend_at env 0 t1) (Suc n) k) (incr_from (Suc n) el) t" by simp
  moreover from tcse have "typecheck (extend_at (extend_at env 0 t2) (Suc n) k) (incr_from (Suc n) er) t" by simp
  ultimately show ?case by (simp add: extend_at_swap)
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
next case ttrv
  thus ?case by simp
next case tpar
  thus ?case by simp
next case (tprl e t1 t2)
  hence "typecheck env (sub_from n e) (Prod t1 t2)" by simp
  thus ?case by simp
next case (tprr e t1 t2)
  hence "typecheck env (sub_from n e) (Prod t1 t2)" by simp
  thus ?case by simp
next case tabt
  thus ?case by simp
next case tinl
  thus ?case by simp
next case tinr
  thus ?case by simp
next case (tcse e t1 t2 el t er)
  hence "typecheck env (sub_from n e) (Sum t1 t2)" by simp 
  moreover from tcse have "typecheck (extend_at env 0 t1) (sub_from (Suc n) el) t" by (simp add: extend_at_swap)
  moreover from tcse have "typecheck (extend_at env 0 t2) (sub_from (Suc n) er) t" by (simp add: extend_at_swap)
  ultimately show ?case by simp
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
next case ttrv
  thus ?case by simp
next case tpar
  thus ?case by simp
next case (tprl e t1 t2)
  hence "typecheck env (subst e e' x) (Prod t1 t2)" by simp
  thus ?case by simp
next case (tprr e t1 t2)
  hence "typecheck env (subst e e' x) (Prod t1 t2)" by simp
  thus ?case by simp
next case tabt
  thus ?case by simp
next case tinl
  thus ?case by simp
next case tinr
  thus ?case by simp
next case (tcse e t1 t2 el t er)
  hence "typecheck env (subst e e' x) (Sum t1 t2)" by (simp add: extend_at_swap) 
  moreover from tcse have "typecheck (extend_at env 0 t1) (subst el (incr_from 0 e') (Suc x)) t" by (simp add: extend_at_swap) 
  moreover from tcse have "typecheck (extend_at env 0 t2) (subst er (incr_from 0 e') (Suc x)) t" by (simp add: extend_at_swap) 
  ultimately show ?case by simp
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
    | "is_val Triv = True"
    | "is_val (Pair e1 e2) = (is_val e1 & is_val e2)"
    | "is_val (ProjL e) = False"
    | "is_val (ProjR e) = False"
    | "is_val (Abort t e) = False"
    | "is_val (InL t t' e) = is_val e"
    | "is_val (InR t t' e) = is_val e"
    | "is_val (Case e el er) = False"

inductive eval :: "expr => expr => bool"
where esuc [simp]: "eval n n' ==> eval (Succ n) (Succ n')"
    | eap1 [simp]: "eval e1 e1' ==> eval (Ap e1 e2) (Ap e1' e2)"
    | eap2 [simp]: "is_val e1 ==> eval e2 e2' ==> eval (Ap e1 e2) (Ap e1 e2')"
    | eap3 [simp]: "is_val e2 ==> eval (Ap (Lam t b) e2) (safe_subst b e2)"
    | eiz1 [simp]: "eval e e' ==> eval (IsZ e0 e1 e) (IsZ e0 e1 e')"
    | eiz2 [simp]: "eval (IsZ e0 e1 Zero) e0"
    | eiz3 [simp]: "is_val e ==> eval (IsZ e0 e1 (Succ e)) (safe_subst e1 e)"
    | efix [simp]: "eval (Fix t b) (safe_subst b (Fix t b))"
    | epa1 [simp]: "eval e1 e1' ==> eval (Pair e1 e2) (Pair e1' e2)"
    | epa2 [simp]: "is_val e1 ==> eval e2 e2' ==> eval (Pair e1 e2) (Pair e1 e2')"
    | epl1 [simp]: "eval e e' ==> eval (ProjL e) (ProjL e')"
    | epl2 [simp]: "is_val e1 ==> is_val e2 ==> eval (ProjL (Pair e1 e2)) e1"
    | epr1 [simp]: "eval e e' ==> eval (ProjR e) (ProjR e')"
    | epr2 [simp]: "is_val e1 ==> is_val e2 ==> eval (ProjR (Pair e1 e2)) e2"
    | eabt [simp]: "eval e e' ==> eval (Abort t e) (Abort t e')"
    | einl [simp]: "eval e e' ==> eval (InL t t' e) (InL t t' e')"
    | einr [simp]: "eval e e' ==> eval (InR t t' e) (InR t t' e')"
    | ecs1 [simp]: "eval e e' ==> eval (Case e el er) (Case e el er)"
    | ecs2 [simp]: "is_val e ==> eval (Case (InL t t' e) el er) (safe_subst el e)"
    | ecs3 [simp]: "is_val e ==> eval (Case (InR t t' e) el er) (safe_subst er e)"

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
      (EX e'. (e = InL t1 t2 e' & is_val e' & typecheck env e' t1)) | (EX e'. (e = InR t1 t2 e' & is_val e' & typecheck env e' t2))"
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
next case epa1
  thus ?case by auto
next case epa2
  thus ?case by auto
next case (epl1 e e')
  hence "!!t2. typecheck env e (Prod t t2) ==> typecheck env e' (Prod t t2)" by simp
  with epl1 have "EX t2. typecheck env e' (Prod t t2)" by auto
  thus ?case by auto
next case epl2
  thus ?case by auto
next case (epr1 e e')
  hence "!!t1. typecheck env e (Prod t1 t) ==> typecheck env e' (Prod t1 t)" by simp
  with epr1 have "EX t1. typecheck env e' (Prod t1 t)" by auto
  thus ?case by auto
next case epr2
  thus ?case by auto
next case eabt
  thus ?case by auto
next case einl
  thus ?case by auto
next case einr
  thus ?case by auto
next case ecs1
  thus ?case by auto
next case ecs2
  thus ?case by auto
next case ecs3
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
next case ttrv
  thus ?case by simp
next case (tpar env e1 t1 e2 t2)
  thus ?case
  proof (cases "is_val e1")
  case True
    hence X: "is_val e1" by simp
    thus ?thesis
    proof (cases "is_val e2")
    case True
      with X show ?thesis by simp  
    next case False
      with tpar have "EX a. eval e2 a" by simp
      hence "EX a. eval (Pair e1 e2) a"
      proof auto
        fix e2'
        assume "eval e2 e2'"
        with True have "eval (Pair e1 e2) (Pair e1 e2')" by simp
        thus "EX a. eval (Pair e1 e2) a" by auto
      qed
      thus ?thesis by simp  
    qed
  next case False
    with tpar have "EX a. eval e1 a" by simp
    hence "EX a. eval (Pair e1 e2) a"
    proof auto
      fix e1'
      assume "eval e1 e1'"
      hence "eval (Pair e1 e2) (Pair e1' e2)" by simp
      thus "EX a. eval (Pair e1 e2) a" by auto
    qed
    with False show ?thesis by simp
  qed
next case (tprl env e t1 t2)
  thus ?case
  proof (cases "is_val e")
  case True
    with tprl have "EX e1 e2. e = Pair e1 e2 & typecheck env e1 t1 & typecheck env e2 t2 & is_val e1 & is_val e2" by (simp add: canonical_prod)
    thus ?thesis
    proof auto
      fix e1 e2
      assume "is_val e1"
         and "is_val e2"
      hence "eval (ProjL (Pair e1 e2)) e1" by simp
      thus "EX a. eval (ProjL (Pair e1 e2)) a" by auto
    qed
  next case False
    with tprl have "EX a. eval e a" by simp
    thus ?thesis
    proof auto
      fix a
      assume "eval e a"
      hence "eval (ProjL e) (ProjL a)" by simp
      thus "EX a. eval (ProjL e) a" by auto
    qed
  qed
next case (tprr env e t1 t2)
  thus ?case
  proof (cases "is_val e")
  case True
    with tprr have "EX e1 e2. e = Pair e1 e2 & typecheck env e1 t1 & typecheck env e2 t2 & is_val e1 & is_val e2" by (simp add: canonical_prod)
    thus ?thesis
    proof auto
      fix e1 e2
      assume "is_val e1"
         and "is_val e2"
      hence "eval (ProjR (Pair e1 e2)) e2" by simp
      thus "EX a. eval (ProjR (Pair e1 e2)) a" by auto
    qed
  next case False
    with tprr have "EX a. eval e a" by simp
    thus ?thesis
    proof auto
      fix a
      assume "eval e a"
      hence "eval (ProjR e) (ProjR a)" by simp
      thus "EX a. eval (ProjR e) a" by auto
    qed
  qed
next case (tabt env e t)
  thus ?case
  proof (cases "is_val e", auto simp add: canonical_void)
    fix x
    assume "eval e x"
    hence "eval (Abort t e) (Abort t x)" by simp
    thus "EX x. eval (Abort t e) x" by auto
  qed
next case (tinl env e t1 t2)
  thus ?case 
  proof (cases "is_val e", auto)
    fix x
    assume "eval e x"
    hence "eval (InL t1 t2 e) (InL t1 t2 x)" by simp
    thus "EX y. eval (InL t1 t2 e) y " by auto
  qed
next case (tinr env e t2 t1)
  thus ?case 
  proof (cases "is_val e", auto)
    fix x
    assume "eval e x"
    hence "eval (InR t1 t2 e) (InR t1 t2 x)" by simp
    thus "EX y. eval (InR t1 t2 e) y " by auto
  qed
next case (tcse env e t1 t2 el t er)
  thus ?case
  proof (cases "is_val e")
  case True
    with tcse have "(EX e'. e = InL t1 t2 e' & is_val e' & typecheck env e' t1) | (EX e'. e = InR t1 t2 e' & is_val e' & typecheck env e' t2)" by (simp add: canonical_sum)
    thus ?thesis
    proof (cases "EX e'. e = InL t1 t2 e'", auto)
      fix e'
      assume "is_val e'" 
      hence "EX x. eval (Case (InL t1 t2 e') el er) (safe_subst el e')" by simp
      thus "EX x. eval (Case (InL t1 t2 e') el er) x" by auto
    next
      fix e'
      assume "is_val e'" 
      hence "EX x. eval (Case (InR t1 t2 e') el er) (safe_subst er e')" by simp
      thus "EX x. eval (Case (InR t1 t2 e') el er) x" by auto
    qed
  next case False
    with tcse have "EX a. eval e a" by simp
    thus ?thesis
    proof auto
      fix a
      assume "eval e a"
      hence "eval (Case e el er) (Case e el er)" by simp
      thus "EX x. eval (Case e el er) x" by auto
    qed
  qed
qed 

end
