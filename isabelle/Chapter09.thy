theory Chapter09
imports Vars AssocList
begin

type_synonym type_env = "(var, type) assoc"

datatype type = Nat | Arr type type

datatype expr = 
  Var var 
| Zero
| Suc expr
| Rec expr var var expr expr
| Lam type var expr
| Ap expr expr

primrec free_vars :: "expr => var set"
where "free_vars (Var v) = {v}"
    | "free_vars Zero = {}"
    | "free_vars (Suc n) = free_vars n"
    | "free_vars (Rec e0 x y e1 e) = free_vars e0 Un free_vars e Un (free_vars e1 - {x, y})"
    | "free_vars (Lam t x b) = free_vars b - {x}"
    | "free_vars (Ap e1 e2) = free_vars e1 Un free_vars e2"

lemma [simp]: "finite (free_vars e)"
by (induction e, simp_all)

primrec bound_vars :: "expr => var set"
where "bound_vars (Var v) = {}"
    | "bound_vars Zero = {}"
    | "bound_vars (Suc n) = bound_vars n"
    | "bound_vars (Rec e0 x y e1 e) = {x, y} Un bound_vars e0 Un bound_vars e Un bound_vars e1"
    | "bound_vars (Lam t x b) = {x} Un bound_vars b"
    | "bound_vars (Ap e1 e2) = bound_vars e1 Un bound_vars e2"

lemma [simp]: "finite (bound_vars e)"
by (induction e, simp_all)

primrec swap_var :: "expr => var => var => expr"
where "swap_var (Var v) n x = Var (if v = x then n else v)"
    | "swap_var Zero n x = Zero"
    | "swap_var (Suc e) n x = Suc (swap_var e n x)"
    | "swap_var (Rec e0 z y e1 e) n x = 
          Rec (swap_var e0 n x) z y (if x = y | x = z then e1 else swap_var e1 n x) (swap_var e n x)"
    | "swap_var (Lam t y b) n x = Lam t y (if x = y then b else swap_var b n x)"
    | "swap_var (Ap e1 e2) n x = Ap (swap_var e1 n x) (swap_var e2 n x)"

lemma [simp]: "size (swap_var e n x) = size e"
by (induction e, simp_all)

primrec subst :: "expr => expr => var => expr"
where "subst (Var v) e x = (if v = x then e else Var v)"
    | "subst Zero e x = Zero"
    | "subst (Suc n) e x = Suc (subst n e x)"
    | "subst (Rec e0 z y e1 et) e x = Rec (subst e0 e x) z y (subst e1 e x) (subst et e x)"
    | "subst (Lam t y b) e x = (
          if x = y then Lam t y b
          else let z = get_free_var (free_vars b Un free_vars e Un bound_vars b Un bound_vars e)
               in let w = get_free_var ({z} Un free_vars b Un free_vars e Un bound_vars b Un bound_vars e)
               in Lam t w (swap_var (swap_var (subst b (swap_var e z y) x) w y) y z))"
    | "subst (Ap e1 e2) e x = Ap (subst e1 e x) (subst e2 e x)"

inductive typecheck :: "(var, type) assoc => expr => type => bool"
where tvar [simp]: "lookup env v = Some t ==> typecheck env (Var v) t"
    | tzer [simp]: "typecheck env Zero Nat"    
    | tsuc [simp]: "typecheck env n Nat ==> typecheck env (Suc n) Nat"
    | trec [simp]: "typecheck env e Nat ==> typecheck env e0 t ==> 
                        typecheck (extend (extend env x Nat) y t) e1 t ==> 
                            typecheck env (Rec e0 x y e1 e) t"
    | tlam [simp]: "typecheck (extend env x r) e t ==> typecheck env (Lam r x e) (Arr r t)"
    | tapp [simp]: "typecheck env e1 (Arr t2 t) ==> typecheck env e2 t2 ==> 
                        typecheck env (Ap e1 e2) t"

inductive_cases [elim!]: "typecheck e (Var x) t"
inductive_cases [elim!]: "typecheck e Zero t"
inductive_cases [elim!]: "typecheck e (Suc x) t"
inductive_cases [elim!]: "typecheck e (Rec x y z w a) t"
inductive_cases [elim!]: "typecheck e (Lam x y z) t"
inductive_cases [elim!]: "typecheck e (Ap x y) t"

lemma [simp]: "typecheck env e t ==> x ~: free_vars e ==> x ~: bound_vars e ==>
                  typecheck (extend env x t') e t"
by (induction env e t rule: typecheck.induct, simp_all)

lemma add_vars_by_unstrip: "typecheck (strip_binding env x) e t ==>
       x ~: free_vars e ==> x ~: bound_vars e ==> typecheck env e t"
proof (induction "strip_binding env x" e t arbitrary: env rule: typecheck.induct)
case tvar
  thus ?case by simp
next case tzer
  thus ?case by simp
next case tsuc
  thus ?case by simp
next case trec
  thus ?case by simp
next case tlam
  thus ?case by simp
next case (tapp e1 t2 t e2 env)
  hence "typecheck env e1 (Arr t2 t)" by simp
  moreover from tapp have "typecheck env e2 t2" by simp
  ultimately show ?case by simp
qed

lemma [simp]: "typecheck (extend (strip_binding env n) x t') e t ==> lookup env n = Some t' ==> 
          n ~: free_vars e ==> n ~: bound_vars e ==> 
              typecheck env (swap_var e n x) t"
proof (induction "extend (strip_binding env n) x t'" e t arbitrary: env rule: typecheck.induct)
case tvar
  thus ?case by auto
next case tzer
  thus ?case by simp
next case tsuc
  thus ?case by simp
next case (trec e e0 t z y e1)
  thus ?case 
  proof (cases "x = y | x = z")
  case True 
    with trec have X: "typecheck (strip_binding (extend (extend env z Nat) y t) n) e1 t" by (cases "x = y", simp_all)
    have "typecheck (strip_binding (extend (extend env z Nat) y t) n) e1 t ==>
            n ~: free_vars e1 ==> n ~: bound_vars e1 ==> typecheck (extend (extend env z Nat) y t) e1 t" by (rule add_vars_by_unstrip)
    with trec X True show ?thesis by simp
  next case False
    hence "x ~= z" by simp
    moreover from False have "x ~= y" by simp
    moreover with trec have "extend (extend (extend (strip_binding env n) z Nat) y t) x t' = extend (strip_binding (extend (extend env z Nat) y t) n) x t'" by simp
    ultimately have "extend (extend (extend (strip_binding env n) x t') z Nat) y t = ..." by simp
    with trec False show ?thesis by simp
  qed
next case (tlam y r b t)
  thus ?case
  proof (cases "x = y")
  case True 
    have "typecheck (strip_binding (extend env y r) n) b t ==> n ~: free_vars b ==> n ~: bound_vars b ==> typecheck (extend env y r) b t" by (rule add_vars_by_unstrip)
    with tlam True show ?thesis by simp
  next case False
    with tlam False show ?thesis by (cases "n = x", simp_all)
  qed
next case (tapp e1 t2 t e2)
  from tapp have "typecheck env (swap_var e1 n x) (Arr t2 t)" by simp
  moreover from tapp have "typecheck env (swap_var e2 n x) t2" by simp
  ultimately show ?case by simp
qed

lemma typecheck_subst: "typecheck (extend env x t') e t ==> typecheck env e' t' ==> 
          typecheck env (subst e e' x) t"
proof (induction "extend env x t'" e t arbitrary: env e' rule: typecheck.induct)
case tvar
  thus ?case by auto
next case tzer
  thus ?case by simp
next case tsuc
  thus ?case by simp
next case trec



  thus ?case sorry
next case (tlam y r b t)
  thus ?case
  proof (cases "x = y")
  case True
    with tlam show ?thesis by simp
  next case False
    def z == "get_free_var (free_vars b Un free_vars e' Un bound_vars b Un bound_vars e')"
    def w == "get_free_var ({z} Un free_vars b Un free_vars e' Un bound_vars b Un bound_vars e')"
    from tlam have "typecheck (extend (extend env x t') y r) b t" by simp
    from tlam have "!!envp ep. extend (extend env x t') y r = extend envp x t' \<Longrightarrow> typecheck envp ep t' \<Longrightarrow> typecheck envp (subst b ep x) t" by simp
    from tlam have "typecheck env e' t'" by simp



    hence "typecheck (extend env w r) (swap_var (swap_var (subst b (swap_var e' z y) x) w y) y z) t" sorry
    with False show ?thesis by (simp add: Let_def z_def w_def)
  qed
next case (tapp e1 t2 t e2)
  from tapp have "typecheck env (subst e1 e' x) (Arr t2 t)" by simp
  moreover from tapp have "typecheck env (subst e2 e' x) t2" by simp
  ultimately show ?case by simp
qed 

end
