theory ConcreteSemantics10_1_Def_Init_Big
  imports Main "~~/src/HOL/IMP/Def_Init_Exp"  "~~/src/HOL/IMP/Def_Init" 
begin 

subsection "Initialization-Sensitive Big Step Semantics"

inductive
  big_step :: "(com \<times> state option) \<Rightarrow> state option \<Rightarrow> bool" (infix "\<Rightarrow>" 55)
where
None: "(c,None) \<Rightarrow> None" |
Skip: "(SKIP,s) \<Rightarrow> s" |
AssignNone: "aval a s = None \<Longrightarrow> (x ::= a, Some s) \<Rightarrow> None" |
Assign: "aval a s = Some i \<Longrightarrow> (x ::= a, Some s) \<Rightarrow> Some(s(x := Some i))" |
Seq:    "(c\<^sub>1,s\<^sub>1) \<Rightarrow> s\<^sub>2 \<Longrightarrow> (c\<^sub>2,s\<^sub>2) \<Rightarrow> s\<^sub>3 \<Longrightarrow> (c\<^sub>1;;c\<^sub>2,s\<^sub>1) \<Rightarrow> s\<^sub>3" |

IfNone:  "bval b s = None \<Longrightarrow> (IF b THEN c\<^sub>1 ELSE c\<^sub>2,Some s) \<Rightarrow> None" |
IfTrue:  "\<lbrakk> bval b s = Some True;  (c\<^sub>1,Some s) \<Rightarrow> s' \<rbrakk> \<Longrightarrow>
  (IF b THEN c\<^sub>1 ELSE c\<^sub>2,Some s) \<Rightarrow> s'" |
IfFalse: "\<lbrakk> bval b s = Some False;  (c\<^sub>2,Some s) \<Rightarrow> s' \<rbrakk> \<Longrightarrow>
  (IF b THEN c\<^sub>1 ELSE c\<^sub>2,Some s) \<Rightarrow> s'" |

WhileNone: "bval b s = None \<Longrightarrow> (WHILE b DO c,Some s) \<Rightarrow> None" |
WhileFalse: "bval b s = Some False \<Longrightarrow> (WHILE b DO c,Some s) \<Rightarrow> Some s" |
WhileTrue:
  "\<lbrakk> bval b s = Some True;  (c,Some s) \<Rightarrow> s';  (WHILE b DO c,s') \<Rightarrow> s'' \<rbrakk> \<Longrightarrow>
  (WHILE b DO c,Some s) \<Rightarrow> s''"

lemmas big_step_induct = big_step.induct[split_format(complete)]

subsection "Soundness wrt Big Steps"

text\<open>Note the special form of the induction because one of the arguments
of the inductive predicate is not a variable but the term \<^term>\<open>Some s\<close>:\<close>

(* Lemma 10.5 (Soundness of D). *)
theorem Sound:
  "\<lbrakk> (c,Some s) \<Rightarrow> s';  D A c A';  A \<subseteq> dom s \<rbrakk>
  \<Longrightarrow> \<exists> t. s' = Some t \<and> A' \<subseteq> dom t"
proof (induction c "Some s" s' arbitrary: s A A' rule:big_step_induct)
(* I failed to show the case of None *)
(*  case None
  then show ?case sorry
next*)
  case Skip
  then show ?case by fastforce
next
  case (AssignNone a s x)
  then show ?case 
    by auto (metis aval_Some option.simps(3) subset_trans)
next
  case (Assign a s i x)
  then show ?case by auto
next
  case (Seq c\<^sub>1 s\<^sub>2 c\<^sub>2 s\<^sub>3)
  then show ?case by auto metis
next
  case (IfNone b s c\<^sub>1 c\<^sub>2)
  then show ?case 
    by auto (metis bval_Some option.simps(3) order_trans)
next
  case (IfTrue b s c\<^sub>1 s' c\<^sub>2)
  then show ?case by auto blast
next
  case (IfFalse b s c\<^sub>2 s' c\<^sub>1)
  then show ?case by auto blast
next
  case (WhileNone b s c)
  then show ?case 
    by auto (metis bval_Some option.simps(3) order_trans)
next
  case (WhileFalse b s c)
  then show ?case by auto
next
  case (WhileTrue b s c s' s'')
  from \<open>D A (WHILE b DO c) A'\<close> obtain A' where "D A c A'" by blast
  then obtain t' where "s' = Some t'" "A \<subseteq> dom s" 
    using WhileTrue.hyps(3) WhileTrue.prems(2) by blast
  then show ?case 
    by (meson D_incr WhileTrue.hyps(3) WhileTrue.hyps(5) WhileTrue.prems(1) \<open>D A c A'\<close> dual_order.trans)
qed

end