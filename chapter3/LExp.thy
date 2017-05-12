section "Arithmetic and Boolean Expressions"

theory LExp 
imports "~~/src/HOL/IMP/BExp"
        "~~/src/HOL/IMP/ASM"
begin

datatype lexp = Nl int | Vl vname | Plusl lexp lexp | LET vname lexp lexp

fun lval :: "lexp \<Rightarrow> state \<Rightarrow> int" where
"lval (Nl n) s = n" |
"lval (Vl x) s = s x" |
"lval (Plusl a\<^sub>1 a\<^sub>2) s = (lval a\<^sub>1 s) + (lval a\<^sub>2 s)" |
"lval (LET x a\<^sub>1 a\<^sub>2) s = (let e = lval a\<^sub>1 s in lval a\<^sub>2 (s(x := e)))"

value "lval (Plusl (Vl ''x'') (Nl 5)) (\<lambda>x. if x = ''x'' then 7 else 0)"
value "lval (Plusl (Vl ''x'') (Nl 5)) ((\<lambda>x. 0) (''x'':= 7))"
value "lval (Plusl (Vl ''x'') (Nl 5)) <''x'':= 7>"
value "lval (Plusl (Vl ''x'') (Nl 5)) <''y'':= 7>"
value "lval (Plusl (Vl ''x'') (Nl 5)) <''x'':= 7, ''x'' := 5>"
value "lval (LET ''y'' (Nl 3) (Plusl (Vl ''y'') (Vl ''x''))) ((\<lambda>x. 0) (''x'':= 7))"

fun asubst :: "vname \<Rightarrow> aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"asubst x a (N n) = N n" |
"asubst x a (V y) = (if x = y then a else V y)" |
"asubst x a (Plus e1 e2) = Plus (asubst x a e1) (asubst x a e2)"

value "asubst ''x'' (N 3) (Plus (V ''x'' ) (V ''y''))"

fun lsubst :: "vname \<Rightarrow> lexp \<Rightarrow> lexp \<Rightarrow> lexp" where
"lsubst x a (Nl n) = Nl n" |
"lsubst x a (Vl y) = (if x = y then a else Vl y)" |
"lsubst x a (Plusl e1 e2) = Plusl (lsubst x a e1) (lsubst x a e2)" |
"lsubst x a (LET y e1 e2) = LET y (lsubst x a e1) (lsubst x a e2)"
  
fun inline :: "lexp \<Rightarrow> aexp" where
"inline (Nl n) = N n" |
"inline (Vl x) = V x" |
"inline (Plusl e1 e2) = Plus (inline e1) (inline e2)" |
"inline (LET x e1 e2) = 
    (let a1 = inline e1 in
     let a2 = inline e2 in
     asubst x a1 a2)"

value "inline (Nl 2)"
value "inline (Vl ''x'')"
value "inline (LET ''x'' (Nl 1) (Vl ''x''))"
value "inline (LET ''x'' (Nl 1) (Plusl (Vl ''y'') (Vl ''x'')))"
value "inline (LET ''x'' (Nl 1) (Plusl (Vl ''x'') (Vl ''x'')))"

lemma aval_subst [simp]:"aval (asubst x a1 a2) s = aval a2 (s(x := aval a1 s))"
apply(induction a2)
apply(auto)
done

lemma "lval a s = aval (inline a) s"
apply(induction a arbitrary: s)
apply(auto)
done
    
end
  
