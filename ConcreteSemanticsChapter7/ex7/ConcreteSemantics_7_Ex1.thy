theory ConcreteSemantics_7_Ex1
  imports Main "~~/src/HOL/IMP/Big_Step"
begin

type_synonym vname = string
datatype aexp = N int | V vname | Plus aexp aexp

fun assigned :: "com \<Rightarrow> vname set" where
"assigned SKIP = {}" |
"assigned (Assign vname aexp) = {vname}"|
"assigned (Seq com1 com2) = (assigned com1) \<union> (assigned com2)"|
"assigned (If bexp com1 com2) = (assigned com1) \<union> (assigned com2)"|
"assigned (While bexp com) = assigned com"

lemma "\<lbrakk>(c, s) \<Rightarrow> t; x \<notin> assigned c\<rbrakk> \<Longrightarrow> s x = t x"
apply(induction rule:big_step_induct)
apply(auto)
done
