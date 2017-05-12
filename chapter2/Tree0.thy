theory Tree0
imports Main
begin

datatype tree0 = Leaf | Node tree0 tree0

fun explode :: "nat \<Rightarrow> tree0 \<Rightarrow> tree0" where
"explode 0 t = t" |
"explode (Suc n) t = explode n (Node t t)"

fun nodes :: "tree0 \<Rightarrow> nat" where
"nodes Leaf = 1" |
"nodes (Node t1 t2) = 1 + nodes t1 + nodes t2"

lemma "nodes (Node t t) = 2 * (nodes t) + 1"
apply(auto)
done

lemma "nodes (explode (Suc n) t) = 2 * nodes (explode n t) + 1"
apply(induction n arbitrary: t)
apply(auto)
done

lemma "nodes (explode n (Node t t)) = 2 * nodes (explode n t) + 1"
apply(induction n arbitrary: t)
apply(auto)
done

lemma "n \<ge> 2 \<Longrightarrow> (n::nat) - 2 + 1 = n - 1"
apply(auto)
done

lemma "nodes (explode n t) = ((nodes t) + 1) * 2 ^ n - 1"
apply(induction n arbitrary: t)
apply(auto simp add:algebra_simps)
done

end
