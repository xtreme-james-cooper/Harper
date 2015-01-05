theory Utilities
imports Main
begin

primrec collect_map :: "('a => 'b option) => 'a list => 'b list option"
where "collect_map f [] = Some []"
    | "collect_map f (a # as) = (case f a of
          None => None
        | Some b => case collect_map f as of
            None => None
          | Some bs => Some (b # bs))"

primrec mapsum :: "('a => nat) => 'a list => nat"
where "mapsum f [] = 0"
    | "mapsum f (a # as) = f a + mapsum f as"

lemma [simp]: "ALL a. size a <= size (f a) ==> size (collect_map f xs) <= size xs"
proof (induction xs)
case Nil
  thus ?case by simp
next case (Cons a as)
  thus ?case by (cases "f a", simp, cases "collect_map f as", simp_all)
qed

lemma [simp]: "length xs = length ys ==> ALL n. f (xs ! n) <= f (ys ! n) ==> 
        mapsum f xs <= mapsum f ys"
proof (induction xs arbitrary: ys)
case Nil
  thus ?case by (induction ys, simp_all)
next case (Cons x xs)
  thus ?case
  proof (induction ys)
  case Nil
    thus ?case by simp
  next case (Cons y ys)
    moreover hence "f x <= f y" by (metis eq_Nil_appendI nth_append_length)
    moreover from Cons have "ALL n. f (xs ! n) <= f (ys ! n)" by (metis (full_types) nth_Cons_Suc)
    ultimately show ?case by fastforce
  qed
qed

end
