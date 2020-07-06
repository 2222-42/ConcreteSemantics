theory Prog_Prove_3_3
  imports Main
begin
lemma "\<forall>x. \<exists>y. x = y"
  by auto

lemma "\<lbrakk>\<forall>xs \<in> A. \<exists>ys. xs = ys @ ys; us \<in> A \<rbrakk> \<Longrightarrow> \<exists>n. length us = n + n"
  by fastforce

lemma "\<lbrakk>\<forall>x y. T x y \<or> T y x;
        \<forall>x y. A x y \<and> A y x \<longrightarrow> x = y;
        \<forall>x y. T x y \<longrightarrow> A x y\<rbrakk>
        \<Longrightarrow> \<forall> x y. A x y \<longrightarrow> T x y"
  by blast

lemma "\<lbrakk> xs @ ys = ys @ xs; length xs = length ys \<rbrakk> \<Longrightarrow> xs = ys "
  using append_eq_append_conv by blast

end