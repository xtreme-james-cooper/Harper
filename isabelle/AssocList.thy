theory AssocList
imports Main
begin

datatype ('a, 'b) assoc = ASSOC "'a => 'b option"

definition empty_map :: "('a, 'b) assoc"
where "empty_map = ASSOC (%x. None)"

primrec extend :: "('a, 'b) assoc => 'a => 'b => ('a, 'b) assoc" 
where "extend (ASSOC env) k v = ASSOC (env(k := Some v))"

primrec lookup :: "('a, 'b) assoc => 'a => 'b option"
where "lookup (ASSOC env) k = env k"

primrec strip_binding :: "('a, 'b) assoc => 'a => ('a, 'b) assoc" 
where "strip_binding (ASSOC env) k = ASSOC (env(k := None))"

lemma [simp]: "lookup empty_map x = None"
by (simp add: empty_map_def)

lemma [simp]: "lookup (extend env k v) k = Some v"
by (induction env, simp)

lemma [simp]: "x ~= k ==> lookup (extend env k v) x = lookup env x"
by (induction env, simp)

lemma [simp]: "k ~= k' ==> extend (extend env k v) k' v' = extend (extend env k' v') k v"
by (induction env, auto)

lemma [simp]: "extend (extend env k v') k v = extend env k v"
by (induction env, simp)

lemma [simp]: "extend (extend (extend env k v'') k' v') k v = extend (extend env k' v') k v"
by (induction env, simp)

lemma [simp]: "strip_binding (extend env k v) k = strip_binding env k"
by (induction env, simp)

lemma [simp]: "extend (strip_binding env k) k v = extend env k v"
by (induction env, simp)

lemma [simp]: "lookup (strip_binding env k) k = None"
by (induction env, simp)

lemma [simp]: "k ~= k' ==> lookup (strip_binding env k) k' = lookup env k'"
by (induction env, simp)

lemma [simp]: "k ~= k' ==> extend (strip_binding env k) k' v = strip_binding (extend env k' v) k"
by (induction env, auto)

lemma [simp]: "lookup env k = Some v ==> extend env k v = env" 
by (induction env, auto)

lemma [simp]: "lookup env k = None ==> strip_binding env k = env" 
by (induction env, auto)

primrec extend_at :: "(nat, 'b) assoc => nat => 'b => (nat, 'b) assoc" 
where "extend_at (ASSOC env) k v = ASSOC (%kp. case kp of
          Suc kpp => if Suc kpp < k then env kp else if Suc kpp = k then Some v else env kpp
        | 0 => if k = 0 then Some v else env kp)"

lemma [simp]: "lookup (extend_at env x v) x = Some v"
by (induction env, cases x, simp_all)

lemma [simp]: "v < n ==> lookup (extend_at env n k) v = lookup env v" 
by (induction env, cases v, simp_all)

lemma [simp]: "v > n ==> lookup (extend_at env n k) v = lookup env (v - 1)" 
by (induction env, cases v, simp_all)

lemma extend_at_swap: "extend_at (extend_at env 0 r) (Suc n) k = extend_at (extend_at env n k) 0 r"
proof (induction env)
case (ASSOC f)
  have "ALL x. (\<lambda>kp. case kp of 0 \<Rightarrow> if Suc n = 0 then Some k else case kp of 0 \<Rightarrow> if 0 = 0 then Some r else f kp | Suc kpp \<Rightarrow> if Suc kpp < 0 then f kp else if Suc kpp = 0 then Some r else f kpp
          | Suc kpp \<Rightarrow> if Suc kpp < Suc n then case kp of 0 \<Rightarrow> if 0 = 0 then Some r else f kp | Suc kpp \<Rightarrow> if Suc kpp < 0 then f kp else if Suc kpp = 0 then Some r else f kpp
                      else if Suc kpp = Suc n then Some k
                           else case kpp of 0 \<Rightarrow> if 0 = 0 then Some r else f kpp | Suc kppa \<Rightarrow> if Suc kppa < 0 then f kpp else if Suc kppa = 0 then Some r else f kppa) x =
    (\<lambda>kp. case kp of 0 \<Rightarrow> if 0 = 0 then Some r else case kp of 0 \<Rightarrow> if n = 0 then Some k else f kp | Suc kpp \<Rightarrow> if Suc kpp < n then f kp else if Suc kpp = n then Some k else f kpp
          | Suc kpp \<Rightarrow> if Suc kpp < 0 then case kp of 0 \<Rightarrow> if n = 0 then Some k else f kp | Suc kpp \<Rightarrow> if Suc kpp < n then f kp else if Suc kpp = n then Some k else f kpp
                      else if Suc kpp = 0 then Some r else case kpp of 0 \<Rightarrow> if n = 0 then Some k else f kpp | Suc kppa \<Rightarrow> if Suc kppa < n then f kpp else if Suc kppa = n then Some k else f kppa) x"
  proof auto
    fix x
    show "(case x of 0 \<Rightarrow> case x of 0 \<Rightarrow> Some r | Suc kpp \<Rightarrow> if Suc kpp < 0 then f x else if Suc kpp = 0 then Some r else f kpp
         | Suc kpp \<Rightarrow> if Suc kpp < Suc 0 then case x of 0 \<Rightarrow> Some r | Suc kpp \<Rightarrow> if Suc kpp < 0 then f x else if Suc kpp = 0 then Some r else f kpp
                     else if Suc kpp = Suc 0 then Some k
                          else case kpp of 0 \<Rightarrow> if (0\<Colon>'d) = (0\<Colon>'d) then Some r else f kpp | Suc kppa \<Rightarrow> if Suc kppa < 0 then f kpp else if Suc kppa = 0 then Some r else f kppa) =
        (case x of 0 \<Rightarrow> Some r
         | Suc kpp \<Rightarrow> if Suc kpp < 0 then case x of 0 \<Rightarrow> Some k | Suc kpp \<Rightarrow> if Suc kpp < 0 then f x else if Suc kpp = 0 then Some k else f kpp
                     else if Suc kpp = 0 then Some r else case kpp of 0 \<Rightarrow> if 0 = 0 then Some k else f kpp | Suc kppa \<Rightarrow> if Suc kppa < 0 then f kpp else if Suc kppa = 0 then Some k else f kppa)"
    proof (cases x)
    case 0
      thus ?thesis by simp
    next case (Suc xx)
      thus ?thesis by (cases xx, simp_all)
    qed
  next
    fix x
    show "(case x of 0 \<Rightarrow> case x of 0 \<Rightarrow> Some r | Suc kpp \<Rightarrow> if Suc kpp < 0 then f x else if Suc kpp = 0 then Some r else f kpp
         | Suc kpp \<Rightarrow> if Suc kpp < Suc n then case x of 0 \<Rightarrow> Some r | Suc kpp \<Rightarrow> if Suc kpp < 0 then f x else if Suc kpp = 0 then Some r else f kpp
                     else if Suc kpp = Suc n then Some k
                          else case kpp of 0 \<Rightarrow> if (0\<Colon>'d) = (0\<Colon>'d) then Some r else f kpp | Suc kppa \<Rightarrow> if Suc kppa < 0 then f kpp else if Suc kppa = 0 then Some r else f kppa) =
        (case x of 0 \<Rightarrow> Some r
         | Suc kpp \<Rightarrow> if Suc kpp < 0 then case x of 0 \<Rightarrow> f x | Suc kpp \<Rightarrow> if Suc kpp < n then f x else if Suc kpp = n then Some k else f kpp
                     else if Suc kpp = 0 then Some r else case kpp of 0 \<Rightarrow> if n = 0 then Some k else f kpp | Suc kppa \<Rightarrow> if Suc kppa < n then f kpp else if Suc kppa = n then Some k else f kppa)"
    proof (cases x)
    case 0
      thus ?thesis by simp
    next case (Suc xx)
      thus ?thesis by (cases xx, simp_all)
    qed
  qed
  thus ?case by auto
qed

lemma [simp]: "extend_at (extend env x k) 0 r = extend (extend_at env 0 r) (Suc x) k"
proof (induction env)
case (ASSOC f)
  have "(\<lambda>kp. case kp of 0 \<Rightarrow> if 0 = 0 then Some r else (f(x \<mapsto> k)) kp | Suc kpp \<Rightarrow> if Suc kpp < 0 then (f(x \<mapsto> k)) kp else if Suc kpp = 0 then Some r else (f(x \<mapsto> k)) kpp) =
    ((\<lambda>kp. case kp of 0 \<Rightarrow> if 0 = 0 then Some r else f kp | Suc kpp \<Rightarrow> if Suc kpp < 0 then f kp else if Suc kpp = 0 then Some r else f kpp)(Suc x \<mapsto> k))" sorry
  thus ?case by auto
qed

lemma [simp]: "extend (extend_at env n k') n k = extend_at env n k"
apply (induction env) apply simp
sorry

lemma [simp]: "lookup env (case x of 0 => undefined | Suc k => k) = lookup (extend_at env 0 r) x" 
apply (induction env) apply (cases x) apply simp defer apply simp
sorry

end
