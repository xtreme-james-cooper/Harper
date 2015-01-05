theory Chapter18_2_Typechecking
imports Chapter18_1_Language
begin

primrec is_ok :: "unit env => expr => bool"
where "is_ok del (Var v) = (lookup del v = Some ())"
    | "is_ok del (Num x) = True"
    | "is_ok del Zero = True"
    | "is_ok del (Succ e) = is_ok del e"
    | "is_ok del (IsZ et e0 es) = (is_ok del et & is_ok del e0 & is_ok (extend del ()) es)"
    | "is_ok del (Lam e) = is_ok (extend del ()) e"
    | "is_ok del (Appl e1 e2) = (is_ok del e1 & is_ok del e2)"
    | "is_ok del (Fix e) = is_ok (extend del ()) e"

lemma [simp]: "is_ok del e ==> n in del ==> is_ok (extend_at n del ()) (insert n e)"
by (induction e arbitrary: n del, fastforce+)

lemma [simp]: "is_ok (extend_at n del ()) e ==> n in del ==> is_ok del e' ==> 
                  is_ok del (subst e' n e)"
by (induction e arbitrary: n del e', fastforce+)

end
