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

value "taval (Plus (Ic 3) (V ''x'')) (\<lambda>x. if x = ''x'' then Iv 4 else I 0) (Iv 7)"
value "taval (Plus (Ic 3) (V ''x'')) ((\<lambda>x. (I 0)) (''x'' := Iv 4)) (Iv 7)"
value "taval (Plus (Ic 3) (V ''x'')) ((\<lambda>x. (R 0)) (''x'' := Rv 4)) (Iv 7)"

end