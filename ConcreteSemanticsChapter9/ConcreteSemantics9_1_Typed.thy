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

end