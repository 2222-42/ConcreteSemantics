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

end