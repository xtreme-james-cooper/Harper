theory Chapter08_1_Language
imports Name
begin

datatype type = 
  NumType 
| StrType
| Arrow type type

datatype expr = 
  Var name
| Num int
| Str string
| Plus expr expr
| Times expr expr
| Cat expr expr
| Len expr
| Let expr "name \<Rightarrow> expr option"
| Lam type "name \<Rightarrow> expr option"
| Appl expr expr

primrec subst :: "expr \<Rightarrow> name \<Rightarrow> expr \<Rightarrow> expr" where 
  "subst e' n (Var x) = (if x = n then e' else Var x)"
| "subst e' n (Num x) = Num x"
| "subst e' n (Str s) = Str s"
| "subst e' n (Plus e1 e2) = Plus (subst e' n e1) (subst e' n e2)"
| "subst e' n (Times e1 e2) = Times (subst e' n e1) (subst e' n e2)"
| "subst e' n (Cat e1 e2) = Cat (subst e' n e1) (subst e' n e2)"
| "subst e' n (Len e) = Len (subst e' n e)"
| "subst e' n (Let e1 e2) =
    Let (subst e' n e1) (\<lambda>x. if x = n then None else map_option (subst e' n) (e2 x))"
| "subst e' n (Lam t e) = 
    Lam t (\<lambda>x. if x = n then None else map_option (subst e' n) (e x))"
| "subst e' n (Appl e1 e2) = Appl (subst e' n e1) (subst e' n e2)"

end
