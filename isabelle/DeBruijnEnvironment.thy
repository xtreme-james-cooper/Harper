theory DeBruijnEnvironment
imports Main
begin

datatype var = DBVar nat

definition first :: var
where "first = DBVar 0"

primrec "next" :: "var => var"
where "next (DBVar v) = DBVar (Suc v)"

fun incr :: "var => var => var"
where "incr (DBVar n) (DBVar v) = DBVar (if v < n then v else Suc v)" 

fun subr :: "var => var => var"
where "subr (DBVar n) (DBVar v) = DBVar (if v < n then v else v - 1)" 

datatype 'a env = DBEnv "'a list"

definition empty_env :: "'a env"
where "empty_env = DBEnv []"

fun is_in :: "var => 'a env => bool" (infix "in" 65)
where "is_in (DBVar n) (DBEnv as) = (n <= length as)"

fun lookup' :: "'a list => nat => 'a option"
where "lookup' [] n = None"
    | "lookup' (a # as) 0 = Some a"
    | "lookup' (a # as) (Suc n) = lookup' as n"

fun lookup :: "'a env => var => 'a option"
where "lookup (DBEnv as) (DBVar n) = lookup' as n"

fun extend_at' :: "nat => 'a list => 'a => 'a list"
where "extend_at' 0 as a' = a' # as"
    | "extend_at' (Suc n) [] a' = undefined"
    | "extend_at' (Suc n) (a # as) a' = a # extend_at' n as a'"

fun extend_at :: "var => 'a env => 'a => 'a env"
where "extend_at (DBVar n) (DBEnv as) a' = DBEnv (extend_at' n as a')"

abbreviation extend :: "'a env => 'a => 'a env"
where "extend == extend_at first"

lemma [simp]: "first in gam"
by (induction gam, simp add: first_def)

lemma [simp]: "x <= length list ==> length (extend_at' x list y) = Suc (length list)"
by (induction x list y rule: extend_at'.induct, simp_all)

lemma [simp]: "x in gam ==> n in gam ==> next n in extend_at x gam y"
by (induction gam, induction x, induction n, simp)

lemma [simp]: "subr n (incr n var) = var"
by (induction n, induction var, simp)

lemma [simp]: "lookup empty_env x = None"
by (cases x, simp add: empty_env_def)

lemma [simp]: "n <= length l ==> length (extend_at' n l a) = Suc (length l)"
by (induction n l a rule: extend_at'.induct, simp_all)

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

lemma [simp]: "n in gam ==> x ~= n ==> 
          lookup (extend_at n gam t) x = lookup gam (subr n x)"
by (induction gam, induction n, induction x, simp)

lemma [simp]: "n in gam ==> lookup (extend_at n gam t) n = Some t"
by (induction gam, induction n, simp)

lemma [simp]: "n in gam ==> lookup gam x = Some t ==> 
         lookup (extend_at n gam t') (incr n x) = Some t"
by (induction gam, induction n, induction x, simp)

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

fun canswap :: "var => var => bool"
where "canswap (DBVar m) (DBVar n) = (m <= n)" 

lemma [simp]: "n in gam ==> canswap m n ==>
        extend_at m (extend_at n gam a) b = extend_at (next n) (extend_at m gam b) a"
by (induction gam, induction n, induction m, simp)

lemma [simp]: "canswap m n ==> incr m (incr n var) = incr (next n) (incr m var)"
by (induction var, induction n, induction m, simp)

lemma [simp]: "canswap first x"
by (induction x, simp add: first_def)

lemma [simp]: "canswap m n ==> canswap (next m) (next n)"
by (induction n, induction m, simp)

lemma [simp]: "n in gam ==> canswap m n ==> m in gam"
by (induction gam, induction n, induction m, simp)

end
