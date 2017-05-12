theory MyNat
imports Main
begin

datatype nat = Zero | Suc nat

fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
"add Zero n = n" | 
"add (Suc m) n = Suc(add m n)"

lemma add_02 [simp]: "add m Zero = m"
apply(induction m) 
apply(auto) 
done

lemma add_assoc [simp]: "add x (add y z) = add (add x y) z"
apply(induction x)
apply(auto)
done

lemma add_suc [simp]: "Suc (add x y) = add x (Suc y)"
apply(induction x)
apply(auto)
done

lemma add_comm [simp]: "add x y = add y x"
apply(induction x)
apply(auto)
done

fun double :: "nat \<Rightarrow> nat" where
"double Zero = Zero" |
"double (Suc m) = Suc (Suc (double m))"

value "double (Suc Zero)"
value "double (Suc (Suc Zero))"

lemma double_add [simp]: "double m = add m m"
apply(induction m)
apply(auto)
done

end