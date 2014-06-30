theory DeBruijn
imports Main
begin

definition redr_set :: "nat set => nat set"
where "redr_set xs = (%n. case n of 0 => undefined | Suc n => n) ` (xs - {0})"

lemma [simp]: "redr_set (a Un b) = redr_set a Un redr_set b"
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
next
  show "!!xa. Suc xa : xs ==> xa < n ==> Suc xa : incr (Suc n) ` xs" by (auto simp add: incr_def)
next 
  fix xa
  assume "Suc xa : xs"
     and "~ xa < n"
  moreover hence "Suc (Suc xa) = incr (Suc n) (Suc xa)" by (simp add: incr_def)
  ultimately show "Suc (Suc xa) : incr (Suc n) ` xs" by blast
qed

lemma [simp]: "redr_set_by k (incr (n + k) ` xs) = incr n ` redr_set_by k xs" 
by (induction k arbitrary: n xs, simp_all)

lemma [simp]: "n ~: incr n ` xs"
proof (auto simp add: incr_def)
  fix x
  show "n = (if x < n then x else Suc x) ==> False" by (cases "x < n", simp_all)
qed

end
