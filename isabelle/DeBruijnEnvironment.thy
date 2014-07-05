theory DeBruijnEnvironment
imports Main
begin

datatype 'a env = DBEnv "'a list"

definition empty_env :: "'a env"
where "empty_env = DBEnv []"

primrec size :: "'a env => nat"
where "size (DBEnv as) = length as"

fun lookup' :: "'a list => nat => 'a option"
where "lookup' [] n = None"
    | "lookup' (a # as) 0 = Some a"
    | "lookup' (a # as) (Suc n) = lookup' as n"

primrec lookup :: "'a env => nat => 'a option"
where "lookup (DBEnv as) n = lookup' as n"

fun extend_at' :: "nat => 'a list => 'a => 'a list"
where "extend_at' 0 as a' = a' # as"
    | "extend_at' (Suc n) [] a' = undefined"
    | "extend_at' (Suc n) (a # as) a' = a # extend_at' n as a'"

primrec extend_at :: "nat => 'a env => 'a => 'a env"
where "extend_at n (DBEnv as) a' = DBEnv (extend_at' n as a')"

abbreviation extend :: "'a env => 'a => 'a env"
where "extend == extend_at 0"

lemma [simp]: "lookup empty_env x = None"
by (simp add: empty_env_def)

lemma [simp]: "n <= length l ==> length (extend_at' n l a) = Suc (length l)"
by (induction n l a rule: extend_at'.induct, simp_all)

lemma [simp]: "n <= size env ==> size (extend_at n env a) = Suc (size env)"
by (induction env, simp)

lemma [simp]: "n <= length l ==> lookup' (extend_at' n l t) x = 
                  (if x < n then lookup' l x else if x > n then lookup' l (x - 1) else Some t)"
proof (induction n l t arbitrary: x rule: extend_at'.induct)
case 1
  thus ?case by (cases x, simp_all)
next case 2
  thus ?case by simp
next case 3
  thus ?case
  proof (cases x)
  case 0
    thus ?thesis by simp
  next case (Suc x')
    with 3 show ?thesis by (cases x', simp_all)
  qed
qed

lemma [simp]: "n <= size gam ==> x ~= n ==> 
          lookup (extend_at n gam t) x = lookup gam (if x < n then x else x - 1)"
by (induction gam, simp)

lemma [simp]: "n <= size gam ==> lookup (extend_at n gam t) n = Some t"
by (induction gam, simp)

lemma [simp]: "ALL x : (%x. x - Suc 0) ` (s - {0}). lookup gam x = lookup gam' x ==> 
                    ALL x : s. lookup (extend_at 0 gam t1) x = lookup (extend_at 0 gam' t1) x"
proof (induction gam, induction gam', auto)
  fix list::"'a list" 
  fix lista x
  assume "ALL x : s - {0}. lookup' lista (x - Suc 0) = lookup' list (x - Suc 0)"
     and "x : s"
  thus "lookup' (t1 # lista) x = lookup' (t1 # list) x" by (induction x, simp, force)
qed

lemma [simp]: "n <= length l ==> m <= n ==> 
          extend_at' m (extend_at' n l a) b = extend_at' (Suc n) (extend_at' m l b) a"
proof (induction n l a arbitrary: m rule: extend_at'.induct)
case 1
  thus ?case by simp
next case 2
  thus ?case by simp
next case (3 n a' as a)
  thus ?case by (cases m, simp_all)
qed

lemma [simp]: "n <= size gam ==> m <= n ==> 
        extend_at m (extend_at n gam a) b = extend_at (Suc n) (extend_at m gam b) a"
by (induction gam, simp)

end
