theory Chapter3
imports "~~/src/HOL/IMP/BExp"
        "~~/src/HOL/IMP/ASM"
begin

text{*
\section*{Chapter 3}

\exercise
To show that @{const asimp_const} really folds all subexpressions of the form
@{term "Plus (N i) (N j)"}, define a function
*}

fun optimal :: "aexp \<Rightarrow> bool" where
"optimal (N i) = True" | 
"optimal (V v) = True" | 
"optimal (Plus (N i) (N j)) = False" |
"optimal (Plus a1 a2) = ((optimal a1) \<or> (optimal a2))"
  
value "optimal (N 0)"
value "optimal (Plus (N 0) (N 1))"

text{*
that checks that its argument does not contain a subexpression of the form
@{term "Plus (N i) (N j)"}. Then prove that the result of @{const asimp_const}
is optimal:
*}

lemma "optimal (asimp_const a)"
apply(induction a rule: optimal.induct)
apply(auto split: aexp.split)
done

text{*
This proof needs the same @{text "split:"} directive as the correctness proof of
@{const asimp_const}. This increases the chance of nontermination
of the simplifier. Therefore @{const optimal} should be defined purely by
pattern matching on the left-hand side,
without @{text case} expressions on the right-hand side.
\endexercise


\exercise
In this exercise we verify constant folding for @{typ aexp}
where we sum up all constants, even if they are not next to each other.
For example, @{term "Plus (N 1) (Plus (V x) (N 2))"} becomes
@{term "Plus (V x) (N 3)"}. This goes beyond @{const asimp}.
Below we follow a particular solution strategy but there are many others.

First, define a function @{text sumN} that returns the sum of all
constants in an expression and a function @{text zeroN} that replaces all
constants in an expression by zeroes (they will be optimized away later):
*}

fun sumN :: "aexp \<Rightarrow> int" where
"sumN (N n) = n" |
"sumN (V x) = 0" |
"sumN (Plus a1 a2) = sumN a1 + sumN a2"

value "sumN (Plus (N 1) (Plus (V x) (N 2)))"

fun zeroN :: "aexp \<Rightarrow> aexp" where
"zeroN (N n) = (N 0)" |
"zeroN (V x) = (V x)" |
"zeroN (Plus a1 a2) = (Plus (zeroN a1) (zeroN a2))"

text {*
Next, define a function @{text sepN} that produces an arithmetic expression
that adds the results of @{const sumN} and @{const zeroN}. Prove that
@{text sepN} preserves the value of an expression.
*}

definition sepN :: "aexp \<Rightarrow> aexp" where
"sepN a = (Plus (N (sumN a)) (zeroN a))"

lemma aval_sepN: "aval (sepN t) s = aval t s"
apply(induction t)
apply(auto simp add: sepN_def)  
done

text {*
Finally, define a function @{text full_asimp} that uses @{const asimp}
to eliminate the zeroes left over by @{const sepN}.
Prove that it preserves the value of an arithmetic expression.
*}

definition full_asimp :: "aexp \<Rightarrow> aexp" where
"full_asimp a = asimp (sepN a)"
  
lemma aval_full_asimp: "aval (full_asimp t) s = aval t s"
apply(induction t)
apply(auto simp add:full_asimp_def aval_sepN)     
done

text{*
\endexercise


\exercise\label{exe:subst}
Substitution is the process of replacing a variable
by an expression in an expression. Define a substitution function
*}

fun subst :: "vname \<Rightarrow> aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"subst x a (N n) = N n" |
"subst x a (V y) = (if x = y then a else V y)" |
"subst x a (Plus a1 a2) = Plus (subst x a a1) (subst x a a2)"

value "subst ''x'' (N 3) (Plus (V ''x'' ) (V ''y''))"

text{*
such that @{term "subst x a e"} is the result of replacing
every occurrence of variable @{text x} by @{text a} in @{text e}.
For example:
@{lemma[display] "subst ''x'' (N 3) (Plus (V ''x'') (V ''y'')) = Plus (N 3) (V ''y'')" by simp}

Prove the so-called \concept{substitution lemma} that says that we can either
substitute first and evaluate afterwards or evaluate with an updated state:
*}

lemma subst_lemma: "aval (subst x a e) s = aval e (s(x := aval a s))"
apply(induction e)
apply(auto)
done

text {*
As a consequence prove that we can substitute equal expressions by equal expressions
and obtain the same result under evaluation:
*}
lemma "aval a1 s = aval a2 s
  \<Longrightarrow> aval (subst x a1 e) s = aval (subst x a2 e) s"
apply(induction a1)
apply(auto simp add: subst_lemma)
done

text{*
\endexercise

\exercise
Take a copy of theory @{theory AExp} and modify it as follows.
Extend type @{typ aexp} with a binary constructor @{text Times} that
represents multiplication. Modify the definition of the functions @{const aval}
and @{const asimp} accordingly. You can remove @{const asimp_const}.
Function @{const asimp} should eliminate 0 and 1 from multiplications
as well as evaluate constant subterms. Update all proofs concerned.
*}

text{*
\endexercise

\exercise
Define a datatype @{text aexp2} of extended arithmetic expressions that has,
in addition to the constructors of @{typ aexp}, a constructor for
modelling a C-like post-increment operation $x{++}$, where $x$ must be a
variable. Define an evaluation function @{text "aval2 :: aexp2 \<Rightarrow> state \<Rightarrow> val \<times> state"}
that returns both the value of the expression and the new state.
The latter is required because post-increment changes the state.

Extend @{text aexp2} and @{text aval2} with a division operation. Model partiality of
division by changing the return type of @{text aval2} to
@{typ "(val \<times> state) option"}. In case of division by 0 let @{text aval2}
return @{const None}. Division on @{typ int} is the infix @{text div}.
*}

text{*
\endexercise

\exercise
The following type adds a @{text LET} construct to arithmetic expressions:
*}

datatype lexp = Nl int | Vl vname | Plusl lexp lexp | LET vname lexp lexp

text{* The @{const LET} constructor introduces a local variable:
the value of @{term "LET x e\<^sub>1 e\<^sub>2"} is the value of @{text e\<^sub>2}
in the state where @{text x} is bound to the value of @{text e\<^sub>1} in the original state.
Define a function @{const lval} @{text"::"} @{typ "lexp \<Rightarrow> state \<Rightarrow> int"}
that evaluates @{typ lexp} expressions. Remember @{term"s(x := i)"}.

Define a conversion @{const inline} @{text"::"} @{typ "lexp \<Rightarrow> aexp"}.
The expression \mbox{@{term "LET x e\<^sub>1 e\<^sub>2"}} is inlined by substituting
the converted form of @{text e\<^sub>1} for @{text x} in the converted form of @{text e\<^sub>2}.
See Exercise~\ref{exe:subst} for more on substitution.
Prove that @{const inline} is correct w.r.t.\ evaluation.
\endexercise


\exercise
Show that equality and less-or-equal tests on @{text aexp} are definable
*}

definition Le :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
"Le a1 a2 = Not (Less a2 a1)"

definition Eq :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
"Eq a1 a2 = And (Le a1 a2) (Le a2 a1)"

text{*
and prove that they do what they are supposed to:
*}

lemma bval_Le: "bval (Le a1 a2) s = (aval a1 s \<le> aval a2 s)"
apply(induction a1)
apply(auto simp add: Le_def)
done

lemma bval_Eq: "bval (Eq a1 a2) s = (aval a1 s = aval a2 s)"
apply(induction a1)
apply(auto simp add: Eq_def Le_def)
done

text{*
\endexercise

\exercise
Consider an alternative type of boolean expressions featuring a conditional: *}

datatype ifexp = Bc2 bool | If ifexp ifexp ifexp | Less2 aexp aexp

text {*  First define an evaluation function analogously to @{const bval}: *}

fun ifval :: "ifexp \<Rightarrow> state \<Rightarrow> bool" where
"ifval (Bc2 v) s = v" |
"ifval (If c b1 b2) s = (if (ifval c s) then (ifval b1 s) else (ifval b2 s))" |
"ifval (Less2 a1 a2) s = ((aval a1 s) < (aval a2 s))"

text{* Then define two translation functions *}

value "true"  
value "True"  
  
fun b2ifexp :: "bexp \<Rightarrow> ifexp" where
"b2ifexp (Bc v) = (Bc2 v)" |
"b2ifexp (Not b) = (If (b2ifexp b) (Bc2 False) (Bc2 True))" |
"b2ifexp (And b1 b2) = (If (b2ifexp b1) (b2ifexp b2) (Bc2 False))" |
"b2ifexp (Less a1 a2) = (Less2 a1 a2)"

fun if2bexp :: "ifexp \<Rightarrow> bexp" where
"if2bexp (Bc2 v) = (Bc v)" |
"if2bexp (If c b1 b2) = (Not (And (Not (And (if2bexp c) (if2bexp b1))) 
                                  (Not (And (Not (if2bexp c)) (if2bexp b2)))))" |
"if2bexp (Less2 a1 a2) = (Less a1 a2)"

text{* and prove their correctness: *}

lemma "bval (if2bexp exp) s = ifval exp s"
apply(induction exp)
apply(auto)  
done

lemma "ifval (b2ifexp exp) s = bval exp s"
apply(induction exp)
apply(auto)  
done

text{*
\endexercise

\exercise
We define a new type of purely boolean expressions without any arithmetic
*}

datatype pbexp =
  VAR vname | NOT pbexp | AND pbexp pbexp | OR pbexp pbexp

text{*
where variables range over values of type @{typ bool},
as can be seen from the evaluation function:
*}

fun pbval :: "pbexp \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> bool" where
"pbval (VAR x) s = s x"  |
"pbval (NOT b) s = (\<not> (pbval b s))" |
"pbval (AND b1 b2) s = ((pbval b1 s) \<and> (pbval b2 s))" |
"pbval (OR b1 b2) s = ((pbval b1 s) \<or> (pbval b2 s))" 

text {* Define a function that checks whether a boolean exression is in NNF
(negation normal form), i.e., if @{const NOT} is only applied directly
to @{const VAR}s: *}

fun is_nnf :: "pbexp \<Rightarrow> bool" where
"is_nnf (VAR x) = True" |
"is_nnf (NOT (VAR x)) = True" |
"is_nnf (NOT b) = False" |
"is_nnf (AND b1 b2) = (is_nnf b1 \<and> is_nnf b2)" |
"is_nnf (OR b1 b2) = (is_nnf b1 \<and> is_nnf b2)"

text{*
Now define a function that converts a @{text bexp} into NNF by pushing
@{const NOT} inwards as much as possible:
*}

fun nnf :: "pbexp \<Rightarrow> pbexp" where
"nnf (VAR x) = (VAR x)" |
"nnf (NOT (VAR x)) = (NOT (VAR x))" |
"nnf (NOT (NOT b)) = nnf b" |
"nnf (NOT (AND b1 b2)) = (OR (nnf (NOT b1)) (nnf (NOT b2)))" |
"nnf (NOT (OR b1 b2)) = (AND (nnf (NOT b1)) (nnf (NOT b2)))" |
"nnf (AND b1 b2) = (AND (nnf b1) (nnf b2))" |
"nnf (OR b1 b2) = (OR (nnf b1) (nnf b2))"

text{*
Prove that @{const nnf} does what it is supposed to do:
*}

lemma pbval_nnf: "pbval (nnf b) s = pbval b s"
apply(induction b rule: nnf.induct)
apply(auto)  
done
    
lemma is_nnf_nnf: "is_nnf (nnf b)"
apply(induction b rule: nnf.induct)
apply(auto)  
done

text{*
An expression is in DNF (disjunctive normal form) if it is in NNF
and if no @{const OR} occurs below an @{const AND}. Define a corresponding
test:
*}

fun no_or :: "pbexp \<Rightarrow> bool" where
"no_or (VAR x) = True" |
"no_or (NOT b) = no_or b" |
"no_or (OR b1 b2) = False" |
"no_or (AND b1 b2) = (no_or b1 \<and> no_or b2)"
  
fun is_dnf :: "pbexp \<Rightarrow> bool" where
"is_dnf (VAR x) = True" |
"is_dnf (NOT (VAR x)) = True" |
"is_dnf (NOT b) = False" |
"is_dnf (AND b1 b2) = (is_nnf b1 \<and> no_or b1 \<and> is_nnf b2 \<and> no_or b2)" |
"is_dnf (OR b1 b2) = (is_dnf b1 \<and> is_dnf b2)"

lemma is_dnf_nnf: "is_dnf b1 \<Longrightarrow> is_nnf b1"
apply(induction b1 rule: is_dnf.induct)
apply(auto)  
done

lemma is_dnf_not_no_or: "is_dnf (NOT v) \<Longrightarrow> no_or v"
apply(induction v rule: is_dnf.induct)
apply(auto)  
done  

text {*
An NNF can be converted into a DNF in a bottom-up manner.
The critical case is the conversion of @{term (sub) "AND b1 b2"}.
Having converted @{text b\<^sub>1} and @{text b\<^sub>2}, apply distributivity of @{const AND}
over @{const OR}. If we write @{const OR} as a multi-argument function,
we can express the distributivity step as follows:
@{text "dist_AND (OR a\<^sub>1 ... a\<^sub>n) (OR b\<^sub>1 ... b\<^sub>m)"}
= @{text "OR (AND a\<^sub>1 b\<^sub>1) (AND a\<^sub>1 b\<^sub>2) ... (AND a\<^sub>n b\<^sub>m)"}. Define
*}

fun dist_AND :: "pbexp \<Rightarrow> pbexp \<Rightarrow> pbexp" where
(*"dist_AND (OR a1 a2) (OR b1 b2) = (OR (OR (dist_AND a1 b1) (dist_AND a1 b2)) (OR (dist_AND a2 b1) (dist_AND a2 b2)))" |*)
"dist_AND a (OR b1 b2) = (OR (dist_AND a b1) (dist_AND a b2))" |
"dist_AND (OR a1 a2) b = (OR (dist_AND a1 b) (dist_AND a2 b))" |
"dist_AND b1 b2 = (AND b1 b2)"

text {* and prove that it behaves as follows: *}

lemma pbval_dist: "pbval (dist_AND b1 b2) s = pbval (AND b1 b2) s"
apply(induction b1 b2 rule: dist_AND.induct)
apply(auto)
done

lemma [simp]:"is_dnf b \<Longrightarrow> is_dnf (dist_AND (NOT (VAR x)) b)"
apply(induction b)
apply(auto simp add: is_dnf_nnf is_dnf_not_no_or)
done

lemma [simp]:"is_dnf b2 \<Longrightarrow>
       is_nnf b1 \<Longrightarrow> no_or b1 \<Longrightarrow> is_nnf b2a \<Longrightarrow> no_or b2a \<Longrightarrow> is_dnf (dist_AND (AND b1 b2a) b2)"
apply(induction b2)
apply(auto simp add: is_dnf_nnf is_dnf_not_no_or)
done

lemma [simp]:"is_dnf (dist_AND b1 b2) \<Longrightarrow>
       is_dnf (dist_AND b2a b2) \<Longrightarrow>
       is_dnf b2 \<Longrightarrow> is_dnf b1 \<Longrightarrow> is_dnf b2a \<Longrightarrow> is_dnf (dist_AND (OR b1 b2a) b2)"
apply(induction b2)
apply(auto simp add: is_dnf_nnf is_dnf_not_no_or)
done
  
lemma is_dnf_dist: "is_dnf b1 \<Longrightarrow> is_dnf b2 \<Longrightarrow> is_dnf (dist_AND b1 b2)"
apply(induction b1 rule: is_dnf.induct)
apply(auto simp add: is_dnf_nnf)
apply(induction b2 rule: dist_AND.induct)
apply(auto simp add: is_dnf_nnf is_dnf_not_no_or)
done

text {* Use @{const dist_AND} to write a function that converts an NNF
  to a DNF in the above bottom-up manner.
*}

fun dnf_of_nnf :: "pbexp \<Rightarrow> pbexp" where
"dnf_of_nnf (VAR x) = (VAR x)" |
"dnf_of_nnf (NOT b) = (NOT b)" |
"dnf_of_nnf (AND b1 b2) = dist_AND (dnf_of_nnf b1) (dnf_of_nnf b2)" |
"dnf_of_nnf (OR b1 b2) = (OR (dnf_of_nnf b1) (dnf_of_nnf b2))"

text {* Prove the correctness of your function: *}

lemma "pbval (dnf_of_nnf b) s = pbval b s"
apply(induction b)
apply(auto simp add:pbval_dist)
done

lemma not_is_dnf_if_nnf: "is_nnf (NOT b) \<Longrightarrow> is_dnf (NOT b)"
apply(induction b)
apply(auto)  
done
    
lemma "is_nnf b \<Longrightarrow> is_dnf (dnf_of_nnf b)"
apply(induction b)
apply(auto simp add:is_dnf_dist not_is_dnf_if_nnf)  
done    

text{*
\endexercise


\exercise\label{exe:stack-underflow}
A \concept{stack underflow} occurs when executing an @{text ADD}
instruction on a stack of size less than two. In our semantics
stack underflow leads to a term involving @{term "hd []"},
which is not an error or exception --- HOL does not
have those concepts --- but some unspecified value. Modify
theory @{theory ASM} such that stack underflow is modelled by @{const None}
and normal execution by @{text Some}, i.e., the execution functions
have return type @{typ "stack option"}. Modify all theorems and proofs
accordingly.
Hint: you may find @{text"split: option.split"} useful in your proofs.
*}

text{*
\endexercise

\exercise\label{exe:register-machine}
This exercise is about a register machine
and compiler for @{typ aexp}. The machine instructions are
*}
type_synonym reg = nat
datatype instr = LDI val reg | LD vname reg | ADD reg reg

text {*
where type @{text reg} is a synonym for @{typ nat}.
Instruction @{term "LDI i r"} loads @{text i} into register @{text r},
@{term "LD x r"} loads the value of @{text x} into register @{text r},
and @{term[names_short] "ADD r\<^sub>1 r\<^sub>2"} adds register @{text r\<^sub>2} to register @{text r\<^sub>1}.

Define the execution of an instruction given a state and a register state;
the result is the new register state: *}

type_synonym rstate = "reg \<Rightarrow> val"

fun exec1 :: "instr \<Rightarrow> state \<Rightarrow> rstate \<Rightarrow> rstate" where
"exec1 (LDI i r) s rs = rs(r := i)" |
"exec1 (LD x r) s rs = rs(r := s(x))" |
"exec1 (ADD r1 r2) s rs = rs(r1 := rs(r1) + rs(r2))"

text{*
Define the execution @{const[source] exec} of a list of instructions as for the stack machine.

The compiler takes an arithmetic expression @{text a} and a register @{text r}
and produces a list of instructions whose execution places the value of @{text a}
into @{text r}. The registers @{text "> r"} should be used in a stack-like fashion
for intermediate results, the ones @{text "< r"} should be left alone.
Define the compiler and prove it correct:
*}

fun execn :: "instr list \<Rightarrow> state \<Rightarrow> rstate \<Rightarrow> rstate" where
"execn [] s rs = rs" |
"execn (i#is) s rs = execn is s (exec1 i s rs)"
  
fun exec :: "instr list \<Rightarrow> state \<Rightarrow> rstate \<Rightarrow> reg \<Rightarrow> val" where
"exec [] s rs r = rs(r)" |
"exec (i#is) s rs r = exec is s (exec1 i s rs) r"

fun comp :: "aexp \<Rightarrow> reg \<Rightarrow> instr list" where
"comp (N n) r = [LDI n r]" |
"comp (V v) r = [LD v r]" |
"comp (Plus a1 a2) r = (comp a1 r) @ (comp a2 (r + 1)) @ [ADD r (r + 1)]"

lemma exec_execn:"exec is1 s rs r = (let rs1 = execn is1 s rs in rs1(r))"
apply(induction is1 arbitrary: rs)
apply(auto)  
done
    
lemma execn_dist_append:"(execn (is1 @ is2) s rs) = (execn is2 s (execn is1 s rs))"
apply(induction is1 arbitrary: rs)
apply(auto)
done

lemma execn_comp_append:"(execn ((comp a r) @ is2) s rs) = (execn is2 s (execn (comp a r) s rs))"
apply(auto simp add:execn_dist_append)
done
      
lemma comp_right_rs_not_changed:"r1 > r \<Longrightarrow> execn (comp a r1) s rs r = rs(r)"
apply(induction a arbitrary: r r1 rs)
apply(auto simp add:execn_dist_append)
done
    
theorem "exec (comp a r) s rs r = aval a s"
apply(induction a arbitrary: r rs)
apply(auto simp add:exec_execn execn_comp_append comp_right_rs_not_changed)
done
    
text{*
\endexercise

\exercise\label{exe:accumulator}
This exercise is a variation of the previous one
with a different instruction set:
*}

datatype instr0 = LDI0 val | LD0 vname | MV0 reg | ADD0 reg

text{*
All instructions refer implicitly to register 0 as a source or target:
@{const LDI0} and @{const LD0} load a value into register 0, @{term "MV0 r"}
copies the value in register 0 into register @{text r}, and @{term "ADD0 r"}
adds the value in register @{text r} to the value in register 0;
@{term "MV0 0"} and @{term "ADD0 0"} are legal. Define the execution functions
*}

fun exec01 :: "instr0 \<Rightarrow> state \<Rightarrow> rstate \<Rightarrow> rstate" where
(* your definition/proof here *)

text{*
and @{const exec0} for instruction lists.

The compiler takes an arithmetic expression @{text a} and a register @{text r}
and produces a list of instructions whose execution places the value of @{text a}
into register 0. The registers @{text "> r"} should be used in a stack-like fashion
for intermediate results, the ones @{text "\<le> r"} should be left alone
(with the exception of 0). Define the compiler and prove it correct:
*}

theorem "exec0 (comp0 a r) s rs 0 = aval a s"
(* your definition/proof here *)

text{*
\endexercise
*}

end

