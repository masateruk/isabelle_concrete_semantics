section "Arithmetic and Boolean Expressions"

theory AExp2 imports Main begin

subsection "Arithmetic Expressions"

type_synonym vname = string
type_synonym val = int
type_synonym state = "vname \<Rightarrow> val"

text_raw{*\snip{AExpaexpdef}{2}{1}{% *}
datatype aexp2 = N int | V vname | Plus aexp2 aexp2 | Div aexp2 aexp2 | Inc vname
text_raw{*}%endsnip*}

text {* A little syntax magic to write larger states compactly: *}

definition null_state ("<>") where
  "null_state \<equiv> \<lambda>x. 0"
syntax 
  "_State" :: "updbinds => 'a" ("<_>")
translations
  "_State ms" == "_Update <> ms"
  "_State (_updbinds b bs)" <= "_Update (_State b) bs"
  
text {* \noindent
  We can now write a series of updates to the function @{text "\<lambda>x. 0"} compactly:
*}
lemma "<a := 1, b := 2> = (<> (a := 1)) (b := (2::int))"
  by (rule refl)

text_raw{*\snip{AExpavaldef}{1}{2}{% *}
fun aval2 :: "aexp2 \<Rightarrow> state \<Rightarrow> (val * state) option" where
"aval2 (N n) s = Some(n, s)" |
"aval2 (V x) s = Some(s x, s)" |
"aval2 (Plus a\<^sub>1 a\<^sub>2) s = 
    (case aval2 a\<^sub>1 s of
         Some(v1, s1) \<Rightarrow> 
              (case aval2 a\<^sub>2 s1 of
                  Some(v2, s2) \<Rightarrow> Some(v1 + v2, s2) |
                  None \<Rightarrow> None) |
         None \<Rightarrow> None)" |
"aval2 (Div a\<^sub>1 a\<^sub>2) s = 
    (case aval2 a\<^sub>1 s of
         Some(v1, s1) \<Rightarrow> 
              (case aval2 a\<^sub>2 s1 of
                  Some(v2, s2) \<Rightarrow> Some(v1 div v2, s2) |
                  None \<Rightarrow> None) |
         None \<Rightarrow> None)" |
"aval2 (Inc x) s = 
    (let v = s x + 1 in
        Some(v, s(x := v)))"
text_raw{*}%endsnip*}

value "aval2 (Plus (V ''x'') (N 5)) (\<lambda>x. if x = ''x'' then 7 else 0)"

text {* The same state more concisely: *}
value "aval2 (Plus (V ''x'') (N 5)) ((\<lambda>x. 0) (''x'':= 7))"
  

text {* In  the @{term[source] "<a := b>"} syntax, variables that are not mentioned are 0 by default:
*}
value "aval2 (Plus (V ''x'') (N 5)) <''y'' := 7>"

value "aval2 (Inc ''x'') <''x'' := 6>"
value "aval2 (Inc ''x'') <''y'' := 6>"

text{* Note that this @{text"<\<dots>>"} syntax works for any function space
@{text"\<tau>\<^sub>1 \<Rightarrow> \<tau>\<^sub>2"} where @{text "\<tau>\<^sub>2"} has a @{text 0}. *}

fun plus :: "aexp2 \<Rightarrow> aexp2 \<Rightarrow> aexp2" where
"plus (N i\<^sub>1) (N i\<^sub>2) = N(i\<^sub>1+i\<^sub>2)" |
"plus (N i) a = (if i=0 then a else Plus (N i) a)" |
"plus a (N i) = (if i=0 then a else Plus a (N i))" |
"plus a\<^sub>1 a\<^sub>2 = Plus a\<^sub>1 a\<^sub>2"

lemma aval_plus[simp]:
  "aval2 (plus a1 a2) s = 
       (case aval2 a1 s of
           Some(v1, s1) \<Rightarrow> 
               (case aval2 a2 s1 of
                   Some(v2, s2) \<Rightarrow> Some(v1 + v2, s2) |
                   None \<Rightarrow> None) |
           None \<Rightarrow> None)"
apply(induction a1 a2 rule: plus.induct)
apply simp_all (* just for a change from auto *)
done

end
  
