theory Div imports Main
begin

fun div2 :: "nat \<Rightarrow> nat" where
"div2 0 = 0" |
"div2 (Suc 0) = 0" |
"div2 (Suc(Suc n)) = Suc(div2 n)"

lemma "div2(n) = n div 2"
apply(induction n rule: div2.induct)



end
