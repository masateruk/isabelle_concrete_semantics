section "Stack Machine and Compilation"

theory ASM imports "~~/src/HOL/IMP/AExp" begin

subsection "Stack Machine"

text_raw{*\snip{ASMinstrdef}{0}{1}{% *}
datatype instr = LOADI val | LOAD vname | ADD
text_raw{*}%endsnip*}

text_raw{*\snip{ASMstackdef}{1}{2}{% *}
type_synonym stack = "val list"
text_raw{*}%endsnip*}

abbreviation "hd2 xs == hd(tl xs)"
abbreviation "tl2 xs == tl(tl xs)"

text{* \noindent Abbreviations are transparent: they are unfolded after
parsing and folded back again before printing. Internally, they do not
exist.*}

text_raw{*\snip{ASMexeconedef}{0}{1}{% *}
fun exec1 :: "instr \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack option" where
"exec1 (LOADI n) _ stk  =  Some(n # stk)" |
"exec1 (LOAD x) s stk  =  Some(s(x) # stk)" |
"exec1  ADD _ []  =  None" |
"exec1  ADD _ [_]  =  None" |
"exec1  ADD _ stk  =  Some((hd2 stk + hd stk) # tl2 stk)"
text_raw{*}%endsnip*}

text_raw{*\snip{ASMexecdef}{1}{2}{% *}
fun exec :: "instr list \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack option" where
"exec [] _ stk = Some(stk)" |
"exec (i#is) s stk = 
  (case (exec1 i s stk) of
    None \<Rightarrow> None
  | Some(stk') \<Rightarrow> exec is s stk')"
text_raw{*}%endsnip*}

value "exec [LOADI 5, LOAD ''y'', ADD] <''x'' := 42, ''y'' := 43> [50]"

lemma exec_append[simp]:
  "exec (is1@is2) s stk = (case (exec is1 s stk) of None \<Rightarrow> None | Some(stk') \<Rightarrow> exec is2 s stk')"
apply(induction is1 arbitrary: stk)
apply(auto split: option.split)
done
    
subsection "Compilation"

text_raw{*\snip{ASMcompdef}{0}{2}{% *}
fun comp :: "aexp \<Rightarrow> instr list" where
"comp (N n) = [LOADI n]" |
"comp (V x) = [LOAD x]" |
"comp (Plus e\<^sub>1 e\<^sub>2) = comp e\<^sub>1 @ comp e\<^sub>2 @ [ADD]"
text_raw{*}%endsnip*}

value "comp (Plus (Plus (V ''x'') (N 1)) (V ''z''))"

theorem exec_comp: "(exec (comp a) s stk) = Some(aval a s # stk)"
apply(induction a arbitrary: stk)  
apply(auto split:option.split)  
done
    
end
