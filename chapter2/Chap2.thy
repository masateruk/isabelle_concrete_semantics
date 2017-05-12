theory Chap2
imports Main

begin

datatype nat = Zero | Suc nat

fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"add Zero n = n" | 
"add (Suc m) n = Suc(add m n)"

lemma add_02: "add m Zero = m"
apply(induction m)
apply(auto)
done

end


