theory ConcreteSemantics9_1_Ex4
  imports "~~/src/HOL/IMP/Star" Complex_Main
begin

section "A Typed Language"

theory Types imports Star Complex_Main begin

text \<open>We build on \<^theory>\<open>Complex_Main\<close> instead of \<^theory>\<open>Main\<close> to access
the real numbers.\<close>

subsection "Arithmetic Expressions"

datatype val = Iv int | Bv bool

type_synonym vname = string
type_synonym state = "vname \<Rightarrow> val"

text_raw\<open>\snip{aexptDef}{0}{2}{%\<close>
datatype exp =  Ic int | V vname | Plus exp exp | Bc bool | Not exp | And exp exp | Less exp exp
text_raw\<open>}%endsnip\<close>

inductive eval :: "exp \<Rightarrow> state \<Rightarrow> val \<Rightarrow> bool" where
"eval (Ic i) s (Iv i)" |
"eval (V x) s (s x)" |
"eval a1 s (Iv i1) \<Longrightarrow> eval a2 s (Iv i2)
 \<Longrightarrow> eval (Plus a1 a2) s (Iv(i1+i2))" |
"eval (Bc v) s (Bv v)" |
"eval b s (Bv v) \<Longrightarrow> eval (Not b) s (Bv (\<not> v))" |
"eval b1 s (Bv v1) \<Longrightarrow> eval b2 s (Bv v2) \<Longrightarrow> eval (And b1 b2) s (Bv (v1 & v2))" |
"eval a1 s (Iv i1) \<Longrightarrow> eval a2 s (Iv i2) \<Longrightarrow> eval (Less a1 a2) s (Bv (i1 < i2))"

inductive_cases [elim!]:
  "eval (Ic i) s v" 
  "eval (V x) s v"
  "eval (Plus a1 a2) s v"
  "eval (Bc b) s v"
  "eval (Not b) s v" 
  "eval (And a1 a2) s v" 
  "eval (Less a1 a2) s v"

subsection "Syntax of Commands"
(* a copy of Com.thy - keep in sync! *)

datatype
  com = SKIP 
      | Assign vname exp       ("_ ::= _" [1000, 61] 61)
      | Seq    com  com         ("_;; _"  [60, 61] 60)
      | If     exp com com     ("IF _ THEN _ ELSE _"  [0, 0, 61] 61)
      | While  exp com         ("WHILE _ DO _"  [0, 61] 61)


subsection "Small-Step Semantics of Commands"

inductive
  small_step :: "(com \<times> state) \<Rightarrow> (com \<times> state) \<Rightarrow> bool" (infix "\<rightarrow>" 55)
where
Assign:  "taval a s v \<Longrightarrow> (x ::= a, s) \<rightarrow> (SKIP, s(x := v))" |

Seq1:   "(SKIP;;c,s) \<rightarrow> (c,s)" |
Seq2:   "(c1,s) \<rightarrow> (c1',s') \<Longrightarrow> (c1;;c2,s) \<rightarrow> (c1';;c2,s')" |

IfTrue:  "tbval b s True \<Longrightarrow> (IF b THEN c1 ELSE c2,s) \<rightarrow> (c1,s)" |
IfFalse: "tbval b s False \<Longrightarrow> (IF b THEN c1 ELSE c2,s) \<rightarrow> (c2,s)" |

While:   "(WHILE b DO c,s) \<rightarrow> (IF b THEN c;; WHILE b DO c ELSE SKIP,s)"

lemmas small_step_induct = small_step.induct[split_format(complete)]

subsection "The Type System"

datatype ty = Ity | Bty

type_synonym tyenv = "vname \<Rightarrow> ty"

inductive typing :: "tyenv \<Rightarrow> exp \<Rightarrow> ty \<Rightarrow> bool"
  ("(1_/ \<turnstile>/ (_ :/ _))" [50,0,50] 50)
where
Ic_ty: "\<Gamma> \<turnstile> Ic i : Ity" |
V_ty: "\<Gamma> \<turnstile> V x : \<Gamma> x" |
Plus_ty: "\<Gamma> \<turnstile> a1 : Ity \<Longrightarrow> \<Gamma> \<turnstile> a2 : Ity \<Longrightarrow> \<Gamma> \<turnstile> Plus a1 a2 : Ity" |
B_ty: "\<Gamma> \<turnstile> Bc v: Bty" |
Not_ty: "\<Gamma> \<turnstile> b:Bty \<Longrightarrow> \<Gamma> \<turnstile> Not b:Bty" |
And_ty: "\<Gamma> \<turnstile> b1:Bty \<Longrightarrow> \<Gamma> \<turnstile> b2:Bty \<Longrightarrow> \<Gamma> \<turnstile> And b1 b2:Bty" |
Less_ty: "\<Gamma> \<turnstile> a1 : Ity \<Longrightarrow> \<Gamma> \<turnstile> a2 : Ity \<Longrightarrow> \<Gamma> \<turnstile> Less a1 a2:Bty"

declare typing.intros [intro!]
inductive_cases [elim!]:
  "\<Gamma> \<turnstile> V x : \<tau>" "\<Gamma> \<turnstile> Ic i : \<tau>" "\<Gamma> \<turnstile> Plus a1 a2 : \<tau>"
 "\<Gamma> \<turnstile> Not b:Bty" "\<Gamma> \<turnstile> And b1 b2:Bty" "\<Gamma> \<turnstile> Less a1 a2:Bty"

text\<open>Warning: the ``:'' notation leads to syntactic ambiguities,
i.e. multiple parse trees, because ``:'' also stands for set membership.
In most situations Isabelle's type system will reject all but one parse tree,
but will still inform you of the potential ambiguity.\<close>


inductive ctyping :: "tyenv \<Rightarrow> com \<Rightarrow> bool" (infix "\<turnstile>" 50) where
Skip_ty: "\<Gamma> \<turnstile> SKIP" |
Assign_ty: "\<Gamma> \<turnstile> a : \<Gamma>(x) \<Longrightarrow> \<Gamma> \<turnstile> x ::= a" |
Seq_ty: "\<Gamma> \<turnstile> c1 \<Longrightarrow> \<Gamma> \<turnstile> c2 \<Longrightarrow> \<Gamma> \<turnstile> c1;;c2" |
If_ty: "\<Gamma> \<turnstile> b:Bty \<Longrightarrow> \<Gamma> \<turnstile> c1 \<Longrightarrow> \<Gamma> \<turnstile> c2 \<Longrightarrow> \<Gamma> \<turnstile> IF b THEN c1 ELSE c2" |
While_ty: "\<Gamma> \<turnstile> b:Bty \<Longrightarrow> \<Gamma> \<turnstile> c \<Longrightarrow> \<Gamma> \<turnstile> WHILE b DO c"

declare ctyping.intros [intro!]
inductive_cases [elim!]:
  "\<Gamma> \<turnstile> x ::= a"  "\<Gamma> \<turnstile> c1;;c2"
  "\<Gamma> \<turnstile> IF b THEN c1 ELSE c2"
  "\<Gamma> \<turnstile> WHILE b DO c"

subsection "Well-typed Programs Do Not Get Stuck"

fun type :: "val \<Rightarrow> ty" where
"type (Iv i) = Ity" |
"type (Bv b) = Bty"

lemma type_eq_Ity[simp]: "type v = Ity \<longleftrightarrow> (\<exists>i. v = Iv i)"
by (cases v) simp_all

lemma type_eq_Bty[simp]: "type v = Bty \<longleftrightarrow> (\<exists>r. v = Bv r)"
by (cases v) simp_all


definition styping :: "tyenv \<Rightarrow> state \<Rightarrow> bool" (infix "\<turnstile>" 50)
where "\<Gamma> \<turnstile> s  \<longleftrightarrow>  (\<forall>x. type (s x) = \<Gamma> x)"

lemma apreservation:
  "\<Gamma> \<turnstile> a : \<tau> \<Longrightarrow> eval a s v \<Longrightarrow> \<Gamma> \<turnstile> s \<Longrightarrow> type v = \<tau>"
apply(induction arbitrary: v rule: typing.induct)
apply (fastforce simp: styping_def)+
done

lemma aprogress: "\<Gamma> \<turnstile> a : \<tau> \<Longrightarrow> \<Gamma> \<turnstile> s \<Longrightarrow> \<exists>v. eval a s v"
proof(induction rule: typing.induct)
  case (Ic_ty \<Gamma> i)
  then show ?case by (auto intro: eval.intros)
next
  case (V_ty \<Gamma> x)
  then show ?case  by (auto intro: eval.intros)
next
  case (Plus_ty \<Gamma> a1 a2)
  then obtain v1 v2 where v: "eval a1 s v1" "eval a2 s v2" by blast
  show ?case 
  proof (cases v1)
    case Iv
    with Plus_ty v show ?thesis
      by (metis apreservation eval.intros(3) ty.distinct(1) type.cases type.simps(2))
  next
    case Bv
    with Plus_ty v show ?thesis
      using apreservation by fastforce
  qed
next
  case (B_ty \<Gamma> v)
  then show ?case 
    using eval.intros(4) by auto
next
  case (Not_ty \<Gamma> b)
  then show ?case 
    by (metis apreservation eval.intros(5) type_eq_Bty)
next
  case (And_ty \<Gamma> b1 b2)
  then show ?case 
    by (metis apreservation eval.intros(6) type_eq_Bty)
next
  case (Less_ty \<Gamma> a1 a2)
  then show ?case 
    by (metis (full_types) apreservation eval.intros(7) type_eq_Ity)
qed

theorem progress:
  "\<Gamma> \<turnstile> c \<Longrightarrow> \<Gamma> \<turnstile> s \<Longrightarrow> c \<noteq> SKIP \<Longrightarrow> \<exists>cs'. (c,s) \<rightarrow> cs'"
proof(induction rule: ctyping.induct)
  case Skip_ty thus ?case by simp
next
  case Assign_ty 
  thus ?case by (metis Assign aprogress)
next
  case Seq_ty thus ?case by simp (metis Seq1 Seq2)
next
  case While_ty show ?case by (metis While)
next
  case (If_ty \<Gamma> b c1 c2)
  then obtain bv where bv_def: "eval b s bv" by (metis aprogress)
  then have "type bv = Bty" using apreservation If_ty by blast
  then show ?case sorry
qed

theorem styping_preservation:
  "(c,s) \<rightarrow> (c',s') \<Longrightarrow> \<Gamma> \<turnstile> c \<Longrightarrow> \<Gamma> \<turnstile> s \<Longrightarrow> \<Gamma> \<turnstile> s'"
proof(induction rule: small_step_induct)
  case Assign thus ?case
    by (auto simp: styping_def) (metis Assign(1,3) apreservation)
qed auto

theorem ctyping_preservation:
  "(c,s) \<rightarrow> (c',s') \<Longrightarrow> \<Gamma> \<turnstile> c \<Longrightarrow> \<Gamma> \<turnstile> c'"
by (induct rule: small_step_induct) (auto simp: ctyping.intros)

abbreviation small_steps :: "com * state \<Rightarrow> com * state \<Rightarrow> bool" (infix "\<rightarrow>*" 55)
where "x \<rightarrow>* y == star small_step x y"

theorem type_sound:
  "(c,s) \<rightarrow>* (c',s') \<Longrightarrow> \<Gamma> \<turnstile> c \<Longrightarrow> \<Gamma> \<turnstile> s \<Longrightarrow> c' \<noteq> SKIP
   \<Longrightarrow> \<exists>cs''. (c',s') \<rightarrow> cs''"
apply(induction rule:star_induct)
apply (metis progress)
  by (metis styping_preservation ctyping_preservation)

end