theory ConcreteSemantics_7_Ex1
  imports Main "~~/src/HOL/IMP/Big_Step"
begin

(* Exercise 7.1. *)
type_synonym vname = string
datatype aexp = N int | V vname | Plus aexp aexp

fun assigned :: "com \<Rightarrow> vname set" where
"assigned SKIP = {}" |
"assigned (Assign vname aexp) = {vname}"|
"assigned (Seq com1 com2) = (assigned com1) \<union> (assigned com2)"|
"assigned (If bexp com1 com2) = (assigned com1) \<union> (assigned com2)"|
"assigned (While bexp com) = assigned com"

(* Try to prove by induction on t, but failed. *)
lemma "\<lbrakk>(c, s) \<Rightarrow> t; x \<notin> assigned c\<rbrakk> \<Longrightarrow> s x = t x"
apply(induction rule:big_step_induct)
apply(auto)
done


(* Exercise 7.2. *)
fun skip :: "com \<Rightarrow> bool" where
"skip SKIP = True" |
"skip (Assign vname aexp) = False"|
"skip (Seq com1 com2) = (skip com1 \<and> skip com2)"|
"skip (If bexp com1 com2) = (skip com1 \<and> skip com2)"|
"skip (While bexp com) = False"
(* 
証明できないと思ったら、明らかにWhileはskip like じゃないでしょ
"skip (While bexp com) = skip com"
もちろん、bexpの値がfalseだったら、skip likeになるが、しかし、環境がここでは変数に含まれていないので、Falseと一律に判定したほうがいい。
*)

lemma "skip c \<Longrightarrow> c \<sim> SKIP"
apply(induction c)
apply(simp_all)
apply fastforce
apply (meson IfE IfFalse IfTrue)
done
