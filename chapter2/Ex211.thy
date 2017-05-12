theory Ex211 
imports Main List
begin

datatype exp = Var | Const int | Add exp exp | Mult exp exp

fun eval :: "exp \<Rightarrow> int \<Rightarrow> int" where
"eval Var x = x" |
"eval (Const n) x = n" |
"eval (Add e1 e2) x = (eval e1 x) + (eval e2 x)" |
"eval (Mult e1 e2) x = (eval e1 x) * (eval e2 x)"

value "eval (Add Var (Const 2)) 1"

fun evalp :: "int list \<Rightarrow> int \<Rightarrow> int" where
"evalp [] x = 0" |
"evalp (y#ys) x = y + ((evalp ys x) * x)"

value "evalp [4,2,-1,3] 0"
value "evalp [4,2,-1,3] 1"
value "evalp [4,2,-1,3] (-1)"
value "evalp [4,2,-1,3] 2"
value "evalp [4*2,2*2,-1*2,3*2] 1"
value "evalp [4*3,2*3,-1*3,3*3] 1"
value "evalp [4*2,2*2,-1*2,3*2] 2"

fun add_pair :: "(int * int) \<Rightarrow> int" where
"add_pair (x, y) = x + y"

value "add_pair (1, 2)"

fun pad_zip :: "int list \<Rightarrow> int list \<Rightarrow> (int * int) list" where
"pad_zip [] [] = []" |
"pad_zip (x#xs) [] = (x, 0) # pad_zip xs []" |
"pad_zip [] (y#ys) = (0, y) # pad_zip [] ys" |
"pad_zip (x#xs) (y#ys) = (x, y) # pad_zip xs ys"

fun add_list :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
"add_list xs ys = map add_pair (pad_zip xs ys)"

value "add_list [1, 2] [3, 4, 5]"

fun merge :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
"merge [] ys = []" |
"merge (x#xs) ys = add_list [ x * y. y <- ys ] (0 # (merge xs ys))"

value "merge [1, 3] [2, 1]"

fun coeffs :: "exp \<Rightarrow> int list" where
"coeffs Var = [0, 1]" |
"coeffs (Const n) = [n]" |
"coeffs (Add e1 e2) = add_list (coeffs e1) (coeffs e2)" |
"coeffs (Mult e1 e2) = merge (coeffs e1) (coeffs e2)"

value "coeffs (Const 1)"
value "coeffs (Const 2)"
value "coeffs (Add (Const 1) (Const 2))"
value "coeffs (Mult (Const 1) (Const 2))"
value "coeffs (Mult (Const 2) Var)"
value "coeffs (Mult (Const 2) (Add (Const 2) Var))"
value "coeffs Var"
value "coeffs (Add (Const 2) Var)"
value "coeffs (Mult Var (Add (Const 2) Var))"
value "coeffs (Mult (Add (Const 3) (Mult (Const 2) Var)) (Add (Const 2) Var))"

lemma [simp]:"evalp (map add_pair (pad_zip xs ys)) x = (evalp xs x) + (evalp ys x)"
apply(induction xs ys rule: pad_zip.induct)
apply(auto simp add:algebra_simps)
done

lemma [simp]:"evalp (map (op * a) ys) x = a * evalp ys x"
apply(induction ys)
apply(auto simp add:algebra_simps)
done

lemma [simp]:"evalp (merge xs ys) x = (evalp xs x) * (evalp ys x)"
apply(induction xs)
apply(auto simp add:algebra_simps)
done

lemma "evalp (coeffs e) x = eval e x"
apply(induction e)
apply(auto)
done

end