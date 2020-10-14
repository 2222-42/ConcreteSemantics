theory ConcreteSemantics10_1_Def_Init_Exp
  imports Main "~~/src/HOL/IMP/Vars" 
begin 
subsection "Initialization-Sensitive Expressions Evaluation"

type_synonym state = "vname \<Rightarrow> val option"

fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val option" where
"aval (N i) s = Some i" |
"aval (V x) s = s x" |
"aval (Plus a\<^sub>1 a\<^sub>2) s =
  (case (aval a\<^sub>1 s, aval a\<^sub>2 s) of
     (Some i\<^sub>1,Some i\<^sub>2) \<Rightarrow> Some(i\<^sub>1+i\<^sub>2) | _ \<Rightarrow> None)"


fun bval :: "bexp \<Rightarrow> state \<Rightarrow> bool option" where
"bval (Bc v) s = Some v" |
"bval (Not b) s = (case bval b s of None \<Rightarrow> None | Some bv \<Rightarrow> Some(\<not> bv))" |
"bval (And b\<^sub>1 b\<^sub>2) s = (case (bval b\<^sub>1 s, bval b\<^sub>2 s) of
  (Some bv\<^sub>1, Some bv\<^sub>2) \<Rightarrow> Some(bv\<^sub>1 & bv\<^sub>2) | _ \<Rightarrow> None)" |
"bval (Less a\<^sub>1 a\<^sub>2) s = (case (aval a\<^sub>1 s, aval a\<^sub>2 s) of
 (Some i\<^sub>1, Some i\<^sub>2) \<Rightarrow> Some(i\<^sub>1 < i\<^sub>2) | _ \<Rightarrow> None)"

(* Lemma 10.1 (Initialized arithmetic expressions). *)
lemma aval_Some: "vars a \<subseteq> dom s \<Longrightarrow> \<exists> i. aval a s = Some i"
  apply(induct a) 
  by(auto)

(* Lemma 10.2 (Initialized boolean expressions). *)
lemma bval_Some: "vars b \<subseteq> dom s \<Longrightarrow> \<exists> bv. bval b s = Some bv"
  apply(induct b)
     apply(auto)
  by (metis aval_Some option.simps(5))

end