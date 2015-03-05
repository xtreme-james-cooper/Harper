theory DeBruijnEnvironment
imports DeBruijnVar
begin

datatype 'a env = DBEnv "'a list"

primrec env_size :: "'a env => nat"
where "env_size (DBEnv as) = length as"

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

fun append :: "'a env => 'a env => 'a env" (infix "+++" 65)
where "DBEnv a +++ DBEnv b = DBEnv (a @ b)"

primrec env_map :: "('a => 'b) => 'a env => 'b env"
where "env_map f (DBEnv n) = DBEnv (map f n)" 

fun update' :: "'a list => nat => 'a => 'a list"
where "update' [] n a = undefined"
    | "update' (b # bs) 0 a = a # bs"
    | "update' (b # bs) (Suc n) a = b # update' bs n a"

fun update :: "'a env => var => 'a => 'a env"
where "update (DBEnv e) (DBVar v) a = DBEnv (update' e v a)" 

lemma [simp]: "first in gam"
by (induction gam, simp add: first_def)

lemma [simp]: "x <= length list ==> length (extend_at' x list y) = Suc (length list)"
by (induction x list y rule: extend_at'.induct, simp_all)

lemma [simp]: "x in gam ==> n in gam ==> next n in extend_at x gam y"
by (induction gam, induction x, induction n, simp)

lemma [simp]: "n in g2 ==> (next_by (env_size g1) n) in (g1 +++ g2)"
by (induction g1, induction g2, induction n, simp)

lemma [simp]: "x in e ==> env_size (extend_at x e y) = Suc (env_size e)"
by (induction x e y rule: extend_at.induct, simp)

lemma [simp]: "env_size empty_env = 0"
by (simp add: empty_env_def)

lemma [elim!]: "env_size gam = 0 ==> gam = empty_env"
by (induction gam, simp add: empty_env_def)

lemma [elim!]: "env_size gam = Suc n ==> EX gam' t. gam = extend gam' t & env_size gam' = n"
proof (induction gam)
case (DBEnv g)
  thus ?case
  proof (cases g, simp)
  case (Cons t g')
    hence "DBEnv g = extend (DBEnv g') t" by (simp add: first_def)
    moreover from DBEnv Cons have "env_size (DBEnv g') = n" by simp
    ultimately show ?thesis by auto
  qed
qed

lemma [simp]: "env_size (e1 +++ e2) = env_size e1 + env_size e2"
by (induction e1, induction e2, simp)

lemma [simp]: "empty_env +++ e = e"
by (induction e, simp add: empty_env_def)

lemma [simp]: "e +++ empty_env = e"
by (induction e, simp add: empty_env_def)

lemma [simp]: "extend e t +++ e' = extend (e +++ e') t"
by (induction e, induction e', simp add: first_def)

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
next case 3
  thus ?case by (cases m, simp_all)
qed

lemma [simp]: "extend_at' (n + length e1) (e1 @ e2) t = e1 @ extend_at' n e2 t"
by (induction e1, simp_all)

lemma [simp]: "extend_at (next_by (env_size e1) n) (e1 +++ e2) t = e1 +++ extend_at n e2 t"
by (induction e1, induction e2, induction n, simp)

lemma [simp]: "n in gam ==> canswap m n ==>
        extend_at m (extend_at n gam a) b = extend_at (next n) (extend_at m gam b) a"
by (induction gam, induction n, induction m, simp)

lemma [simp]: "n in gam ==> canswap m n ==> m in gam"
by (induction gam, induction n, induction m, simp)

lemma [simp]: "env_map f empty_env = empty_env"
by (simp add: empty_env_def)

lemma [simp]: "lookup' env x = Some v ==> lookup' (map f env) x = Some (f v)"
by (induction env x rule: lookup'.induct, simp_all)

lemma [simp]: "lookup env x = Some v ==> lookup (env_map f env) x = Some (f v)"
by (induction env, induction x, simp)
                
lemma [elim]: "inj f ==> lookup' (map f env) x = Some (f v) ==> lookup' env x = Some v"
by (induction env x rule: lookup'.induct, simp, simp add: inj_on_def, fastforce) 

lemma [elim]: "inj f ==> lookup (env_map f env) x = Some (f v) ==> lookup env x = Some v"
by (induction env, induction x, auto)

lemma [simp]: "n <= length env ==> extend_at' n (map f env) (f t) = map f (extend_at' n env t)" 
by (induction n env t rule: extend_at'.induct, simp_all)

lemma [simp]: "n in env ==> extend_at n (env_map f env) (f t) = env_map f (extend_at n env t)" 
by (induction env, induction n, simp)

lemma [simp]: "n in env ==> n in env_map f env" 
by (induction env, induction n, simp)

lemma [simp]: "env_map f (env_map g env) = env_map (f o g) env"
by (induction env, simp)

lemma [simp]: "lookup' (map f env) n = Some t ==> EX t'. t = f t'"
by (induction env n rule: lookup'.induct, auto)

lemma [simp]: "lookup (env_map f env) n = Some t ==> EX t'. t = f t'"
by (induction env, induction n, simp)

end
