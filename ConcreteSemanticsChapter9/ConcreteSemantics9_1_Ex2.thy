theory ConcreteSemantics9_1_Ex2
  imports Main "~~/src/HOL/IMP/Types" 
begin

fun atyp :: "tyenv \<Rightarrow> aexp \<Rightarrow> ty "
where
"atyp \<Gamma> (Ic i) = Ity" |
"atyp \<Gamma> (Rc r) = Rty" |
"atyp \<Gamma> (V x) = \<Gamma> x" |
"atyp \<Gamma> (Plus a1 a2) = 
  (case (atyp \<Gamma> a1, atyp \<Gamma> a2)of 
  (Ity, Ity) \<Rightarrow> Ity |
  (_, _) \<Rightarrow> Rty 
)"


fun aval :: "aexp => state => val" where
"aval (Ic i) s = (Iv i)" |
"aval (Rc r) s = (Rv r)" |
"aval (V x) s = s x" |
"aval (Plus a1 a2) s = 
  (case (aval a1 s, aval a2 s) of
    (Iv i1, Iv i2) \<Rightarrow> Iv(i1+i2) |
    (Iv i1, Rv r2) \<Rightarrow> Rv(real_of_int(i1)+r2) |
    (Rv r1, Iv i2) \<Rightarrow> Rv(r1+real_of_int(i2)) |
    (Rv r1, Rv r2) \<Rightarrow> Rv(r1+r2)
)"

(*
lemma "atyp \<Gamma> a1 = type (aval a1 s) \<Longrightarrow>
       atyp \<Gamma> a2 = type (aval a2 s) \<Longrightarrow>
       \<Gamma> \<turnstile> s \<Longrightarrow>
       (case type (aval a1 s) of Ity \<Rightarrow> case type (aval a2 s) of Ity \<Rightarrow> Ity | Rty \<Rightarrow> Rty | Rty \<Rightarrow> Rty) =
       type
        (case aval a1 s of Iv i1 \<Rightarrow> case aval a2 s of Iv i2 \<Rightarrow> Iv (i1 + i2) | Rv r2 \<Rightarrow> Rv (real_of_int i1 + r2)
         | Rv r1 \<Rightarrow> case aval a2 s of Iv i2 \<Rightarrow> Rv (r1 + real_of_int i2) | Rv r2 \<Rightarrow> Rv (r1 + r2))"
  sledgehammer*)

theorem "\<Gamma> \<turnstile> s \<Longrightarrow> atyp \<Gamma> a = type (aval a s)"
  apply(induction a)
     apply auto
   apply (simp add: styping_def)
  by (smt ty.exhaust ty.simps(3) ty.simps(4) type_eq_Ity type_eq_Rty val.simps(5) val.simps(6))


end