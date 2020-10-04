theory Concrete_Semantics_2_4_ex9
imports Main
begin

fun add:: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"add 0 n = n" |
"add (Suc m) n = Suc(add m n)"


fun itadd :: "nat => nat => nat" where
"itadd 0 n = n" |
"itadd (Suc m) n = itadd m (Suc n)"

lemma add_03[simp]: "add m (Suc n) = Suc (add m n)"
apply(induction m arbitrary: n)
apply(auto)
done

lemma "itadd m n = add m n"
apply(induction m arbitrary: n)
apply(auto)
done

end