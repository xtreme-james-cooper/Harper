theory DeBruijn
imports Main
begin

definition redr_set :: "nat set => nat set"
where "redr_set xs = (%n. case n of 0 => undefined | Suc n => n) ` (xs - {0})"

lemma [simp]: "redr_set (a Un b) = redr_set a Un redr_set b"
by (auto simp add: redr_set_def)

lemma [simp]: "0 ~: a ==> redr_set (insert 0 a) = redr_set a"
by (auto simp add: redr_set_def)

lemma [simp]: "redr_set {0} = {}"
by (auto simp add: redr_set_def)

lemma [simp]: "redr_set (a - {Suc x}) = redr_set a - {x}"
proof (auto simp add: redr_set_def) 
  fix n
  assume "0 < n" 
     and "n ~= Suc (case n of 0 => undefined | Suc n => n)"
  thus False by (cases n, simp_all)
qed

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

lemma [simp]: "redr_set_by n (a Un b) = redr_set_by n a Un redr_set_by n b"
by (induction n arbitrary: a b, simp_all)

lemma [simp]: "redr_set_by n (a - {x + n}) = redr_set_by n a - {x}"
by (induction n arbitrary: a, simp_all)

lemma [simp]: "(x : redr_set_by n xs) = (x + n : xs)" 
by (induction n arbitrary: xs, simp_all)

definition incr :: "nat => nat => nat"
where "incr n v = (if v < n then v else Suc v)"

lemma [simp]: "incr (Suc n) 0 = 0"
by (simp add: incr_def)

lemma [simp]: "incr 0 x = Suc x"
by (simp add: incr_def)

lemma [simp]: "m <= n ==> incr m (incr n x) = incr (Suc n) (incr m x)"
by (simp add: incr_def)

lemma [simp]: "incr (Suc m) (Suc x) = Suc (incr m x)"
by (simp add: incr_def)

lemma [simp]: "v < m ==> (v : incr m ` s) = (v : s)"
by (auto simp add: incr_def)

lemma [simp]: "m <= v ==> (Suc v : incr m ` s) = (v : s)" 
proof auto
  fix x
  show "m \<le> v \<Longrightarrow> Suc v = incr m x \<Longrightarrow> x \<in> s \<Longrightarrow> v \<in> s" 
  by (cases "x < m", simp_all add: incr_def)
next
  have "m \<le> v \<Longrightarrow> v \<in> s \<Longrightarrow> Suc v \<in> (%v. incr m v) ` s" by (simp add: incr_def)
  thus "m \<le> v \<Longrightarrow> v \<in> s \<Longrightarrow> Suc v \<in> incr m ` s" by simp
qed

definition subr :: "nat => nat => nat"
where "subr n v = (if v < n then v else v - 1)"

lemma [simp]: "subr (Suc n) 0 = 0"
by (simp add: subr_def)

lemma [simp]: "m < n ==> incr m (subr n x) = subr (Suc n) (incr m x)"
by (auto simp add: incr_def subr_def)

definition expand_set_at :: "nat => nat set => nat set"
where "expand_set_at n s = insert n (incr n ` s)"

definition expand_set :: "nat set => nat set"
where "expand_set s = insert 0 (incr 0 ` s)"

lemma [simp]: "expand_set (expand_set_at n s) = expand_set_at (Suc n) (expand_set s)"
proof (auto simp add: expand_set_at_def expand_set_def incr_def)
  fix xb
  assume "(if xb < n then Suc xb else Suc (Suc xb)) \<notin> incr 0 ` incr n ` s" and "xb \<in> s"
  thus False by (cases "xb < n", simp_all)
qed

lemma [simp]: "P (expand_set_at 0 s) ==> P (expand_set s)"
by (simp add: expand_set_at_def expand_set_def)

lemma [simp]: "redr_set (incr 0 ` xs) = xs" 
by (auto simp add: incr_def)

lemma [simp]: "redr_set (incr (Suc n) ` xs) = incr n ` redr_set xs" 
proof (auto simp add: incr_def)
  fix x xa
  assume "Suc x = (if xa < Suc n then xa else Suc xa)"
     and "xa : xs" 
  thus "x : incr n ` redr_set xs"
  proof (cases xa, auto)
    fix xb
    assume "Suc xb : xs"
       and "Suc x = (if xb < n then Suc xb else Suc (Suc xb))"
    moreover hence "x = incr n xb" by (auto simp add: incr_def)
    ultimately show "x : incr n ` redr_set xs" by simp
  qed
qed

lemma [simp]: "redr_set_by k (incr (n + k) ` xs) = incr n ` redr_set_by k xs" 
by (induction k arbitrary: n xs, simp_all)

lemma [simp]: "n ~: incr n ` xs"
proof (auto simp add: incr_def)
  fix x
  show "n = (if x < n then x else Suc x) ==> False" by (cases "x < n", simp_all)
qed

lemma [simp]: "(Suc n : incr 0 ` s) = (n : s)"
using incr_def by (metis image_iff less_nat_zero_code nat.inject)

lemma [simp]: "(incr m v : expand_set_at m s) = (v : s)"
by (simp add: expand_set_at_def incr_def)



end
