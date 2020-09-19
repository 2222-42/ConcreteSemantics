theory ConcreteSemantics9_1_Typed
  imports Main "~~/src/HOL/IMP/Star" Complex_Main
begin                                                 

subsection "Arithmetic Expressions"

datatype val = Iv int | Rv real

type_synonym vname = string
type_synonym state = "vname \<Rightarrow> val"

text_raw\<open>\snip{aexptDef}{0}{2}{%\<close>
datatype aexp =  Ic int | Rc real | V vname | Plus aexp aexp
text_raw\<open>}%endsnip\<close>

inductive taval :: "aexp \<Rightarrow> state \<Rightarrow> val \<Rightarrow> bool" where
"taval (Ic i) s (Iv i)" |
"taval (Rc r) s (Rv r)" |
"taval (V x) s (s x)" |
"taval a1 s (Iv i1) \<Longrightarrow> taval a2 s (Iv i2)
 \<Longrightarrow> taval (Plus a1 a2) s (Iv(i1+i2))" |
"taval a1 s (Rv r1) \<Longrightarrow> taval a2 s (Rv r2)
 \<Longrightarrow> taval (Plus a1 a2) s (Rv(r1+r2))"

inductive_cases [elim!]:
  "taval (Ic i) s v"  
  "taval (Rc i) s v"
  "taval (V x) s v"
  "taval (Plus a1 a2) s v"

subsection "Boolean Expressions"

datatype bexp = Bc bool | Not bexp | And bexp bexp | Less aexp aexp

inductive tbval :: "bexp \<Rightarrow> state \<Rightarrow> bool \<Rightarrow> bool" where
"tbval (Bc v) s v" |
"tbval b s bv \<Longrightarrow> tbval (Not b) s (\<not> bv)" |
"tbval b1 s bv1 \<Longrightarrow> tbval b2 s bv2 \<Longrightarrow> tbval (And b1 b2) s (bv1 & bv2)" |
"taval a1 s (Iv i1) \<Longrightarrow> taval a2 s (Iv i2) \<Longrightarrow> tbval (Less a1 a2) s (i1 < i2)" |
"taval a1 s (Rv r1) \<Longrightarrow> taval a2 s (Rv r2) \<Longrightarrow> tbval (Less a1 a2) s (r1 < r2)"

subsection "Syntax of Commands"
(* a copy of Com.thy - keep in sync! *)

datatype
  com = SKIP 
      | Assign vname aexp       ("_ ::= _" [1000, 61] 61)
      | Seq    com  com         ("_;; _"  [60, 61] 60)
      | If     bexp com com     ("IF _ THEN _ ELSE _"  [0, 0, 61] 61)
      | While  bexp com         ("WHILE _ DO _"  [0, 61] 61)


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

value "(''x'' ::= V ''y'';; ''y''  ::= Plus (V ''x'') (V ''y''), s(''y'' := Iv 7))"

value "(''x'' ::= V ''y'';; ''y''  ::= Plus (V ''x'') (V ''y''), s(''y'' := Iv 7)) \<rightarrow>
(SKIP;; ''y'' ::= Plus (V ''x'') (V ''y''), s(''x'':= Iv 7, ''y'' := Iv 7))"
value "(SKIP;; ''y'' ::= Plus (V ''x'') (V ''y''), s(''x'':= Iv 7)) \<rightarrow>
(''y'' ::= Plus (V ''x'') (V ''y''), s(''x'' := Iv 7))"
value "(''y'' ::= Plus (V ''x'') (V ''y''), s(''x'' := Iv 7)) \<rightarrow>
(SKIP, s(''x'' := Iv 7,''y'' := Iv 14))"

value "(''x'' ::= V ''y'';; ''y''  ::= Plus (V ''x'') (Rc 3), s(''y'' := Iv 7))"
value "(''x'' ::= V ''y'';; ''y''  ::= Plus (V ''x'') (Rc 3), s(''y'' := Iv 7)) \<rightarrow>
(SKIP;; ''y'' ::= Plus (V ''x'') (Rc 3), s(''x'':= Iv 7))"
value "(SKIP;; ''y'' ::= Plus (V ''x'') (Rc 3), s(''x'':= Iv 7)) \<rightarrow>
(''y'' ::= Plus (V ''x'') (Rc 3), s(''x'' := Iv 7))"

lemma "(SKIP;; ''y'' ::= Plus (V ''x'') (Rc 3), s(''x'':= Iv 7)) \<rightarrow>
(''y'' ::= Plus (V ''x'') (Rc 3), s(''x'' := Iv 7))"
  by (simp add: Seq1)
(*
after that no further execution
step is possible because we cannot find an execution for taval on the righthand
side of the second assignment
lemma "(''y'' ::= Plus (V ''x'') (Rc 3), s(''x'' := Iv 7, ''y'' := Iv 7)) \<rightarrow>
(SKIP, s(''x'' := Iv 7, ''y'' := Rc 10))"
*)

subsection "The Type System"

datatype ty = Ity | Rty

type_synonym tyenv = "vname \<Rightarrow> ty"

inductive atyping :: "tyenv \<Rightarrow> aexp \<Rightarrow> ty \<Rightarrow> bool"
  ("(1_/ \<turnstile>/ (_ :/ _))" [50,0,50] 50)
where
Ic_ty: "\<Gamma> \<turnstile> Ic i : Ity" |
Rc_ty: "\<Gamma> \<turnstile> Rc r : Rty" |
V_ty: "\<Gamma> \<turnstile> V x : \<Gamma> x" |
Plus_ty: "\<Gamma> \<turnstile> a1 : \<tau> \<Longrightarrow> \<Gamma> \<turnstile> a2 : \<tau> \<Longrightarrow> \<Gamma> \<turnstile> Plus a1 a2 : \<tau>"

declare atyping.intros [intro!]
inductive_cases [elim!]:
  "\<Gamma> \<turnstile> V x : \<tau>" "\<Gamma> \<turnstile> Ic i : \<tau>" "\<Gamma> \<turnstile> Rc r : \<tau>" "\<Gamma> \<turnstile> Plus a1 a2 : \<tau>"

inductive btyping :: "tyenv \<Rightarrow> bexp \<Rightarrow> bool" (infix "\<turnstile>" 50)
where
B_ty: "\<Gamma> \<turnstile> Bc v" |
Not_ty: "\<Gamma> \<turnstile> b \<Longrightarrow> \<Gamma> \<turnstile> Not b" |
And_ty: "\<Gamma> \<turnstile> b1 \<Longrightarrow> \<Gamma> \<turnstile> b2 \<Longrightarrow> \<Gamma> \<turnstile> And b1 b2" |
Less_ty: "\<Gamma> \<turnstile> a1 : \<tau> \<Longrightarrow> \<Gamma> \<turnstile> a2 : \<tau> \<Longrightarrow> \<Gamma> \<turnstile> Less a1 a2"

declare btyping.intros [intro!]
inductive_cases [elim!]: "\<Gamma> \<turnstile> Not b" "\<Gamma> \<turnstile> And b1 b2" "\<Gamma> \<turnstile> Less a1 a2"

text\<open>Warning: the ``:'' notation leads to syntactic ambiguities,
i.e. multiple parse trees, because ``:'' also stands for set membership.
In most situations Isabelle's type system will reject all but one parse tree,
but will still inform you of the potential ambiguity.\<close>

inductive ctyping :: "tyenv \<Rightarrow> com \<Rightarrow> bool" (infix "\<turnstile>" 50) where
Skip_ty: "\<Gamma> \<turnstile> SKIP" |
Assign_ty: "\<Gamma> \<turnstile> a : \<Gamma>(x) \<Longrightarrow> \<Gamma> \<turnstile> x ::= a" |
Seq_ty: "\<Gamma> \<turnstile> c1 \<Longrightarrow> \<Gamma> \<turnstile> c2 \<Longrightarrow> \<Gamma> \<turnstile> c1;;c2" |
If_ty: "\<Gamma> \<turnstile> b \<Longrightarrow> \<Gamma> \<turnstile> c1 \<Longrightarrow> \<Gamma> \<turnstile> c2 \<Longrightarrow> \<Gamma> \<turnstile> IF b THEN c1 ELSE c2" |
While_ty: "\<Gamma> \<turnstile> b \<Longrightarrow> \<Gamma> \<turnstile> c \<Longrightarrow> \<Gamma> \<turnstile> WHILE b DO c"

declare ctyping.intros [intro!]
inductive_cases [elim!]:
  "\<Gamma> \<turnstile> x ::= a"  "\<Gamma> \<turnstile> c1;;c2"
  "\<Gamma> \<turnstile> IF b THEN c1 ELSE c2"
  "\<Gamma> \<turnstile> WHILE b DO c"

value "\<Gamma> ''y'' = Ity \<Longrightarrow>  \<Gamma> ''x'' = Ity  \<Longrightarrow> (\<Gamma> \<turnstile> ''x'' ::= V ''y'';; ''y'' ::= Plus (V ''x'') (V''y''))"

subsection "Well-typed Programs Do Not Get Stuck"

fun type :: "val \<Rightarrow> ty" where
"type (Iv i) = Ity" |
"type (Rv r) = Rty"

lemma type_eq_Ity[simp]: "type v = Ity \<longleftrightarrow> (\<exists>i. v = Iv i)"
by (cases v) simp_all

lemma type_eq_Rty[simp]: "type v = Rty \<longleftrightarrow> (\<exists>r. v = Rv r)"
by (cases v) simp_all

definition styping :: "tyenv \<Rightarrow> state \<Rightarrow> bool" (infix "\<turnstile>" 50)
  where "\<Gamma> \<turnstile> s  \<longleftrightarrow>  (\<forall>x. type (s x) = \<Gamma> x)"

(* Lemma 9.2 (Preservation for arithmetic expressions). *)
lemma apreservation:
  "\<Gamma> \<turnstile> a : \<tau> \<Longrightarrow> taval a s v \<Longrightarrow> \<Gamma> \<turnstile> s \<Longrightarrow> type v = \<tau>"
apply(induction arbitrary: v rule: atyping.induct)
     apply (fastforce simp: styping_def)+
  done

(* Lemma 9.3 (Progress for arithmetic expressions). *)
lemma aprogress: "\<Gamma> \<turnstile> a : \<tau> \<Longrightarrow> \<Gamma> \<turnstile> s \<Longrightarrow> \<exists>v. taval a s v"
proof(induction rule: atyping.induct)
case (Ic_ty \<Gamma> i)
  then show ?case 
    using taval.intros(1) by auto
next
case (Rc_ty \<Gamma> r)
  then show ?case 
    using taval.intros(2) by auto
next
  case (V_ty \<Gamma> x)
  then show ?case 
    using taval.intros(3) by auto
next
case (Plus_ty \<Gamma> a1 \<tau> a2)
  then show ?case 
    by (metis apreservation taval.intros(4) taval.intros(5) ty.distinct(1) type.elims)
qed

(* Lemma 9.4 (Progress for boolean expressions). *)
lemma bprogress: "\<Gamma> \<turnstile> b \<Longrightarrow> \<Gamma> \<turnstile> s \<Longrightarrow> \<exists>v. tbval b s v"
proof(induction rule: btyping.induct)
case (B_ty \<Gamma> v)
  then show ?case 
    using tbval.intros(1) by blast
next
case (Not_ty \<Gamma> b)
  then show ?case 
    using tbval.intros(2) by blast
next
  case (And_ty \<Gamma> b1 b2)
  then show ?case 
    using tbval.intros(3) by blast
next
  case (Less_ty \<Gamma> a1 \<tau> a2)
  then obtain v1 v2 where v: "taval a1 s v1" "taval a2 s v2" 
    using aprogress by blast
  show ?case 
  proof (cases v1)
    case (Iv x1)
    then show ?thesis 
      (* by (fastforce intro!: tbval.intros(4) dest!:apreservation) *)
      by (metis Less_ty.hyps(1) Less_ty.hyps(2) Less_ty.prems \<open>\<And>thesis. (\<And>v1 v2. \<lbrakk>taval a1 s v1; taval a2 s v2\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> apreservation tbval.intros(4) tbval.intros(5) ty.distinct(1) type.elims)
  next
    case (Rv x2)
    then show ?thesis 
      (* by (fastforce intro!: tbval.intros(5) dest!:apreservation) *)
      by (metis Less_ty.hyps(1) Less_ty.hyps(2) Less_ty.prems \<open>\<And>thesis. (\<And>v1 v2. \<lbrakk>taval a1 s v1; taval a2 s v2\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> apreservation tbval.intros(4) tbval.intros(5) ty.distinct(1) type.elims)
  qed
qed

(* Theorem 9.5 (Preservation: commands stay well-typed). *)
theorem ctyping_preservation:"(c,s) \<rightarrow> (c',s') \<Longrightarrow> \<Gamma> \<turnstile> c \<Longrightarrow> \<Gamma> \<turnstile>c'"
  apply(induction rule: small_step_induct)
       apply (simp add: Skip_ty)
  by blast+
(*proof (induction rule:small_step_induct)
  case (Assign a s v x)
  then show ?case 
    by (simp add: Skip_ty)
next
  case (Seq1 c s)
  then show ?case 
    by blast
next
  case (Seq2 c1 s c1' s' c2)
  then show ?case 
    by blast
next
  case (IfTrue b s c1 c2)
  then show ?case by blast
next
  case (IfFalse b s c1 c2)
  then show ?case by blast
next
  case (While b c s)
  then show ?case by blast
qed*)

(* Theorem 9.6 (Preservation: states stay well-typed). *)
theorem styping_preservation:
  "(c,s) \<rightarrow> (c',s') \<Longrightarrow> \<Gamma> \<turnstile> c \<Longrightarrow> \<Gamma> \<turnstile> s \<Longrightarrow> \<Gamma> \<turnstile> s'"
proof(induction rule: small_step_induct)
case (Assign a s v x)
  then show ?case 
    using apreservation styping_def by fastforce
next
case (Seq1 c s)
  then show ?case 
    by simp
next
  case (Seq2 c1 s c1' s' c2)
  then show ?case 
    by blast
next
case (IfTrue b s c1 c2)
  then show ?case 
    by simp
next
  case (IfFalse b s c1 c2)
  then show ?case 
    by blast
next
  case (While b c s)
  then show ?case 
    by simp
qed

(* Theorem 9.7 (Progress for commands). *)
theorem progress:
  "\<Gamma> \<turnstile> c \<Longrightarrow> \<Gamma> \<turnstile> s \<Longrightarrow> c \<noteq> SKIP \<Longrightarrow> \<exists>cs'. (c,s) \<rightarrow> cs'"
proof(induction rule: ctyping.induct)
case (Skip_ty \<Gamma>)
  then show ?case 
    by simp
next
case (Assign_ty \<Gamma> a x)
  then show ?case 
    using Assign aprogress by blast
next
  case (Seq_ty \<Gamma> c1 c2)
  then show ?case 
    by (metis Seq1 Seq2 old.prod.exhaust)
next
  case (If_ty \<Gamma> b c1 c2)
  then obtain vb where v: "tbval b s vb" 
    using bprogress by blast
  show ?case 
  proof(cases vb)
    case True
    then show ?thesis 
      using IfTrue v by fastforce
  next
    case False
    then show ?thesis 
      using IfFalse v by fastforce
  qed
next
  case (While_ty \<Gamma> b c)
  then show ?case 
    using While by blast
qed

abbreviation small_steps :: "com * state \<Rightarrow> com * state \<Rightarrow> bool" (infix "\<rightarrow>*" 55)
where "x \<rightarrow>* y == star small_step x y"

(* Theorem 9.8 (Type soundness). *)
theorem type_sound:
  "(c,s) \<rightarrow>* (c',s') \<Longrightarrow> \<Gamma> \<turnstile> c \<Longrightarrow> \<Gamma> \<turnstile> s \<Longrightarrow> c' \<noteq> SKIP
   \<Longrightarrow> \<exists>cs''. (c',s') \<rightarrow> cs''"
  apply(induction rule:star_induct)
  using progress apply blast
  using ctyping_preservation styping_preservation by blast

subsection "excercises"

subsubsection "Exercise 9.1."
fun atype :: "tyenv \<Rightarrow> aexp \<Rightarrow> ty option"
where
"atype \<Gamma> (Ic i) = Some Ity" |
"atype \<Gamma> (Rc r) = Some Rty" |
"atype \<Gamma> (V x) = Some (\<Gamma> x)" |
"atype \<Gamma> (Plus a1 a2) = (if (atype \<Gamma> a1) = (atype \<Gamma> a2) then atype \<Gamma> a1 else None)"

fun bok :: "tyenv \<Rightarrow> bexp \<Rightarrow> bool"
where
"bok \<Gamma> (Bc v) = True" |
"bok \<Gamma> (Not b) = bok \<Gamma> b" |
"bok \<Gamma> (And b1 b2) = (bok \<Gamma> b1 \<and> bok \<Gamma> b2)" |
"bok \<Gamma> (Less a1 a2) = (if atype \<Gamma> a1 = atype \<Gamma> a2 then (\<exists> a. atype \<Gamma> a1 = Some a) else False) "

fun cok :: "tyenv \<Rightarrow> com \<Rightarrow> bool"  where
"cok \<Gamma> SKIP = True" |
"cok \<Gamma> (x ::= a) = (atype \<Gamma> a = Some (\<Gamma> x))" |
"cok \<Gamma> (c1;;c2) = (cok \<Gamma> c1 \<and> cok \<Gamma> c2) " |
"cok \<Gamma> (IF b THEN c1 ELSE c2) = (bok \<Gamma> b \<and> cok \<Gamma> c1 \<and> cok \<Gamma> c2)" |
"cok \<Gamma> (WHILE b DO c) = (bok \<Gamma> b \<and> cok \<Gamma> c)"

lemma atyping_to_atype: "(\<Gamma> \<turnstile> a: t) = (atype \<Gamma> a = Some t)"
  apply(induction a)
     apply(auto)
  done

lemma btyping_to_bok: "(\<Gamma> \<turnstile> b) = bok \<Gamma> b"
  apply(induction b)
  apply(auto simp add: atyping_to_atype)
  done

lemma "(\<Gamma> \<turnstile> c) = cok \<Gamma> c"
  apply(induction c)
      apply(auto simp add: atyping_to_atype btyping_to_bok)
  done

(* Exercise 9.2. *)

(* Exercise 9.3 *)

end