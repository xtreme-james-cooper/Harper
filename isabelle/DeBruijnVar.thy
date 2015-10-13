theory DeBruijnVar
imports Main
begin

datatype var = DBVar nat

definition first :: var where 
  "first = DBVar 0"

primrec "next" :: "var \<Rightarrow> var" where 
  "next (DBVar v) = DBVar (Suc v)"

primrec next_by :: "nat \<Rightarrow> var \<Rightarrow> var" where 
  "next_by n (DBVar v) = DBVar (v + n)"

fun incr :: "var \<Rightarrow> var \<Rightarrow> var" where 
  "incr (DBVar n) (DBVar v) = DBVar (if v < n then v else Suc v)" 

fun subr :: "var \<Rightarrow> var \<Rightarrow> var" where 
  "subr (DBVar n) (DBVar v) = DBVar (if v > n then v - 1 else v)" 

fun canswap :: "var \<Rightarrow> var \<Rightarrow> bool" where 
  "canswap (DBVar m) (DBVar n) = (m \<le> n)" 

lemma [simp]: "subr n (incr n var) = var"
  by (induction n, induction var) simp

lemma [simp]: "incr n n = next n"
  by (induction n) simp

lemma [simp]: "next v \<noteq> v"
  by (induction v) simp

lemma [simp]: "subr v (next v) = v"
  by (induction v) simp

lemma [simp]: "incr v x \<noteq> v"
  by (induction v, induction x) simp

lemma [simp]: "next_by 0 v = v"
  by (induction v) simp

lemma [simp]: "next_by x (next v) = next (next_by x v)"
  by (induction v) simp

lemma [simp]: "next_by (Suc x) v = next (next_by x v)"
  by (induction v) simp

lemma [simp]: "canswap m n \<Longrightarrow> incr m (incr n var) = incr (next n) (incr m var)"
  by (induction var, induction n, induction m) simp

lemma [simp]: "canswap first x"
  by (induction x) (simp add: first_def)

lemma [simp]: "canswap m n \<Longrightarrow> canswap m (next n)"
  by (induction n, induction m) simp

lemma [simp]: "canswap m n \<Longrightarrow> canswap (next m) (next n)"
  by (induction n, induction m) simp

lemma [simp]: "canswap m n \<Longrightarrow> canswap (next_by x m) (next_by x n)"
  by (induction n, induction m) simp

lemma [simp]: "canswap var del \<Longrightarrow> canswap (incr n var) (next del)"
  by (induction del, induction n, induction var) simp

lemma [simp]: "canswap n del \<Longrightarrow> canswap v (next del) \<Longrightarrow> canswap (subr n v) del"
  by (induction del, induction n, induction v) auto

lemma [simp]: "canswap m n \<Longrightarrow> incr m (subr n v) = subr (next n) (incr m v)"
  by (induction m, induction n, induction v) auto

lemma [simp]: "canswap m n \<Longrightarrow> incr m n = next n"
  by (induction m, induction n) simp

lemma [elim]: "canswap m n \<Longrightarrow> m = next n \<Longrightarrow> False"
  by (induction m, induction n) simp

lemma [simp]: "canswap m n \<Longrightarrow> v \<noteq> n \<Longrightarrow> incr m v \<noteq> next n"
  by (induction m, induction n, induction v) simp

lemma [simp]: "canswap (next m) n \<Longrightarrow> incr n m = m"
  by (induction m, induction n) simp

lemma [simp]: "canswap m n \<Longrightarrow> v \<noteq> m \<Longrightarrow> incr (next n) v \<noteq> m"
  by (induction m, induction n, induction v) simp

lemma [simp]: "canswap m n \<Longrightarrow> v \<noteq> m \<Longrightarrow> subr m (incr (next n) v) = incr n (subr m v)"
  by (induction m, induction n, induction v) auto

lemma [simp]: "canswap m n \<Longrightarrow> subr (next n) m = m"
  by (induction m, induction n) simp

end
