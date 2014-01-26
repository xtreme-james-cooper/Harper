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

end
