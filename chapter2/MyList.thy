theory MyList
imports Main
begin

fun itrev :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"itrev [] ys = ys" |
"itrev (x#xs) ys = itrev xs (x#ys)"

lemma [simp]:"itrev xs ys = rev xs @ ys"
apply(induction xs arbitrary: ys)
apply(auto)
done

lemma "itrev xs [] = rev xs"
apply(induction xs)
apply(auto)
done

fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"add 0 n = n" |
"add (Suc m) n = Suc (add m n)"


fun iadd :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"iadd 0 n = n" |
"iadd (Suc m) n = iadd m (Suc n)"

value "iadd 3 2"
value "iadd 2 0"
value "iadd 0 0"

lemma [simp] : "add m (Suc n) = Suc (add m n)"
apply(induction m)
apply(auto)
done

lemma "iadd m n = add m n"
apply(induction m arbitrary: n)
apply(auto)
done

end