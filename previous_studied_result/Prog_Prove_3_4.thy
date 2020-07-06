theory Prog_Prove_3_4
  imports Main
begin

lemma "\<lbrakk> (a::nat) \<le> x + b; 2 * x < c \<rbrakk> \<Longrightarrow> 2 * a + 1 \<le> 2 * b + c"
  by arith

lemma "\<lbrakk> (a::nat) \<le> b; b \<le> c; c \<le> d; d \<le> e \<rbrakk> \<Longrightarrow> a \<le> e"
  by(blast intro: le_trans)

thm conjI[OF refl[of "a"] refl[of "b"]]

lemma "Suc(Suc(Suc a)) \<le> b \<Longrightarrow> a \<le> b"
  by (blast dest: Suc_leD)

end