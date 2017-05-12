theory Ex2
imports Main
begin

fun count :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
"count n [] = 0" |
"count n (x # xs) = (if x = n then 1 + count n xs else count n xs)"

value "count 1 []"
value "count 1 [1]"

lemma count_lt_length [simp]: "count x xs \<le> length xs"
apply(induction xs)
apply(auto)
done

(* Ex 2.4 *)
fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
"snoc [] x = [x]" | 
"snoc (x # xs) y = (x # (snoc xs y))"

fun reverse :: "'a list \<Rightarrow> 'a list" where
"reverse [] = []" |
"reverse (x # xs) = snoc (reverse xs) x"

value "reverse [1,2,3]"

lemma snoc_rev [simp]: "reverse (snoc xs a) = a # (reverse xs)"
apply(induction xs)
apply(auto)
done

lemma rev_rev [simp]: "reverse (reverse xs) = xs"
apply(induction xs)
apply(auto)
done

(* Ex 2.5 *)
fun sum :: "nat \<Rightarrow> nat" where
"sum 0 = 0" |
"sum (Suc n) = (Suc n) + (sum n)"

value "(sum 3)"
value "(4 div 2)::nat"

lemma sum_bin [simp]: "sum n = n * (n + 1) div 2"
apply(induction n)
apply(auto)
done

end
