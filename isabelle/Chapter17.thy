theory Chapter17
imports DeBruijnEnvironment
begin

datatype expr = 
  Var var
| Lam expr
| Appl expr expr

primrec insert :: "var => expr => expr"
where "insert n (Var v) = Var (incr n v)"
    | "insert n (Lam e) = Lam (insert (next n) e)"
    | "insert n (Appl e1 e2) = Appl (insert n e1) (insert n e2)"

primrec remove :: "var => expr => expr"
where "remove n (Var v) = Var (subr n v)"
    | "remove n (Lam e) = Lam (remove (next n) e)"
    | "remove n (Appl e1 e2) = Appl (remove n e1) (remove n e2)"

primrec subst' :: "var => expr => expr => expr"
where "subst' n e' (Var v) = (if v = n then e' else Var v)"
    | "subst' n e' (Lam e) = Lam (subst' (next n) (insert first e') e)"
    | "subst' n e' (Appl e1 e2) = Appl (subst' n e' e1) (subst' n e' e2)"

definition subst :: "expr => expr => expr"
where "subst e' e = remove first (subst' first (insert first e') e)"

lemma [simp]: "remove n (insert n e) = e"
by (induction e arbitrary: n, simp_all)

lemma [simp]: "canswap m n ==> insert m (insert n e) = insert (next n) (insert m e)"
by (induction e arbitrary: n m, simp_all)

lemma [simp]: "remove v (subst' v (insert v e') (insert v e)) = e"
by (induction e arbitrary: e' v, simp_all)

lemma [simp]: "subst e' (insert first e) = e"
by (simp add: subst_def)

primrec is_ok :: "unit env => expr => bool"
where "is_ok del (Var x) = (lookup del x = Some ())"
    | "is_ok del (Lam e) = is_ok (extend del ()) e"
    | "is_ok del (Appl e1 e2) = (is_ok del e1 & is_ok del e2)"

lemma [simp]: "is_ok gam e ==> n in gam ==> 
         is_ok (extend_at n gam ()) (insert n e)"
by (induction e arbitrary: n gam, fastforce+)

lemma [simp]: "is_ok (extend_at n gam ()) e ==> n in gam ==> is_ok gam e' ==> 
        is_ok gam (remove n (subst' n (insert n e') e))"
by (induction e arbitrary: n gam e', fastforce+)

lemma [simp]: "is_ok (extend gam ()) e ==> is_ok gam e' ==> is_ok gam (subst e' e)"
by (simp add: subst_def)

primrec is_val :: "expr => bool"
where "is_val (Var v) = False"
    | "is_val (Lam e) = True"
    | "is_val (Appl e1 e2) = False"

inductive eval :: "expr => expr => bool"
where eval_appl_1 [simp]: "eval e1 e1' ==> eval (Appl e1 e2) (Appl e1' e2)"
    | eval_appl_2 [simp]: "is_val e1 ==> eval e2 e2' ==> eval (Appl e1 e2) (Appl e1 e2')"
    | eval_appl_3 [simp]: "is_val e2 ==> eval (Appl (Lam e1) e2) (subst e2 e1)"

theorem preservation: "eval e e' ==> is_ok del e ==> is_ok del e'"
by (induction e e' rule: eval.induct, fastforce+)

theorem progress: "is_ok del e ==> del = empty_env ==> is_val e | (EX e'. eval e e')"
proof (induction e)
case Var
  thus ?case by simp
next case Lam
  thus ?case by simp
next case Appl
  thus ?case by (metis eval.intros expr.exhaust is_ok.simps(3) is_val.simps(1) is_val.simps(3))
qed

end
