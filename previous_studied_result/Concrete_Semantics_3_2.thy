theory Concrete_Semantics_3_2
  imports Main
begin 
(* from 3.1 *) 
type_synonym vname = string
datatype aexp = N int | V vname | Plus aexp aexp
type_synonym val = int
type_synonym state = "vname \<Rightarrow> val" 

fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
"aval (N n) s = n" |
"aval (V x) s = s x" |
"aval (Plus a b) s = aval a s + aval b s" 

fun plus :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"plus (N i1) (N i2) = N(i1+i2)" |                       
"plus (N i) a = (if i=0 then a else Plus (N i) a)" |
"plus a (N i) = (if i=0 then a else Plus a (N i))" |
"plus a1 a2 = Plus a1 a2"

fun asimp :: "aexp \<Rightarrow> aexp" where
"asimp (N n) = N n" |
"asimp (V x ) = V x" |
"asimp (Plus a1 a2) = plus (asimp a1) (asimp a2)"

(* from 3.1 *)

datatype bexp = Bc bool | Not bexp | And bexp bexp | Less aexp aexp

fun bval :: "bexp \<Rightarrow> state \<Rightarrow> bool" where
"bval (Bc v) s = v" |
"bval (Not b) s = (\<not> bval b s)" |
"bval (And b1 b2) s = (bval b1 s \<and> bval b2 s)" |
"bval (Less a1 a2) s = (aval a1 s < aval a2 s)"

fun not :: "bexp \<Rightarrow> bexp" where
"not (Bc True) = Bc False" |
"not (Bc False) = Bc True" |
"not b =  Not b"

fun "and" :: "bexp \<Rightarrow> bexp \<Rightarrow> bexp" where
"and (Bc True) b = b" |
"and b (Bc True) = b" |
"and (Bc False) b = Bc False" |
"and b (Bc False) = Bc False" |
"and b1 b2 = And b1 b2"

fun less :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
"less (N n1) (N n2) = Bc(n1 < n2)" |
"less a1 a2 = Less a1 a2"

fun bsimp :: "bexp \<Rightarrow> bexp" where
"bsimp (Bc v) = Bc v" |
"bsimp (Not b) = not(bsimp b)" |
"bsimp (And b1 b2) = and (bsimp b1) (bsimp b2)" |
"bsimp (Less a1 a2) = less (asimp a1) (asimp a2)"

fun Eq :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
"Eq a b = And (Not(Less a b))  (Not(Less b a))"

fun Le :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
"Le a b = Not (And (Not (Less a b))  (Not(Eq a b)))"

lemma "bval (Eq a1 a2) s = (aval a1 s = aval a2 s)"
  apply(auto)
  done

lemma "bval (Le a1 a2) s = (aval a1 s \<le> aval a2 s)"
  apply(auto)
  done

datatype ifexp = Bc2 bool | If ifexp ifexp ifexp | Less2 aexp aexp

fun ifval :: "ifexp \<Rightarrow> state \<Rightarrow> bool" where
"ifval (Bc2 v) s = v" |
"ifval (If a b c) s = (if (ifval a s) then (ifval b s) else (ifval c s))" |
"ifval (Less2 a1 a2) s = (aval a1 s < aval a2 s)"

fun b2ifexp :: "bexp \<Rightarrow> ifexp" where
"b2ifexp (Bc v) = Bc2 v" |
"b2ifexp (Not b) = If (b2ifexp b) (Bc2 False) (Bc2 True)" |
"b2ifexp (And b1 b2) = If (b2ifexp b1)  (b2ifexp  b2) (Bc2 False)" |
"b2ifexp (Less a1 a2) = Less2  a1 a2"

fun if2bexp :: "ifexp \<Rightarrow> bexp" where
"if2bexp (Bc2 v) = Bc v" |
"if2bexp (Less2 a b) = Less a b" |
"if2bexp (If a b c) = And (Not (And (if2bexp a) (Not (if2bexp b))))(Not (And (Not (if2bexp a)) (Not (if2bexp c))))"

lemma "bval b s = ifval (b2ifexp b) s"
  apply(induction b)
  apply(auto)
  done

lemma "ifval i s = bval (if2bexp i) s"
  apply(induction i)
  apply(auto)
  done

datatype pbexp = VAR vname | NOT pbexp | AND pbexp pbexp | OR pbexp pbexp

fun pbval :: "pbexp \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> bool" where     
"pbval (VAR x ) s = s x" |
"pbval (NOT b) s = (\<not> pbval b s)" |
"pbval (AND b1 b2) s = (pbval b1 s \<and> pbval b2 s)" |
"pbval (OR b1 b2) s = (pbval b1 s \<or> pbval b2 s)"

fun is_nnf :: "pbexp \<Rightarrow> bool" where
"is_nnf (VAR x) = True" |
"is_nnf (NOT (VAR x)) = True" |
"is_nnf (NOT y) = False" |
"is_nnf (OR a b) = (is_nnf a \<and> is_nnf b)" |
"is_nnf (AND a b) = (is_nnf a \<and> is_nnf b)"

(* pushing NOT inwards as much as possible *)
fun nnf :: "pbexp \<Rightarrow> pbexp" where
"nnf (VAR x) = VAR x" |
"nnf (NOT (VAR x)) = NOT (VAR x)" |
"nnf (NOT (NOT a)) = nnf a" |
"nnf (NOT (OR  a b)) = AND (nnf (NOT a)) (nnf (NOT b))" |
"nnf (NOT (AND  a b)) = OR (nnf (NOT a)) (nnf (NOT b))" |
"nnf (AND  a  b) = AND (nnf a) (nnf b)" |
"nnf (OR  a  b) = OR (nnf a) (nnf b)"
                                      
lemma nnf_preserv : "pbval (nnf b) s = pbval b s"
  apply(induction b rule: nnf.induct)                  
  apply(auto)                                 
  done                                           

fun is_dnf :: "pbexp \<Rightarrow> bool" where
"is_dnf (VAR x) = True"|  
"is_dnf (NOT y) = True" |
"is_dnf (OR a b) = (is_dnf a \<and> is_dnf b)" |
"is_dnf (AND (OR a b) c) = False" | 
"is_dnf (AND a (OR b c)) = False" |
"is_dnf (AND a b) =  (is_dnf a \<and> is_dnf b)"
                                        
fun mk_dnf_conj :: "pbexp \<Rightarrow> pbexp \<Rightarrow> pbexp" where
"mk_dnf_conj e (OR a b) = OR (mk_dnf_conj e a) (mk_dnf_conj e b)" |
"mk_dnf_conj (OR a b) e  = OR (mk_dnf_conj a e) (mk_dnf_conj b e)" |
"mk_dnf_conj x  y  = AND x y"
             
lemma mk_dnf_preserv : "pbval (mk_dnf_conj a b) s = (pbval a s \<and> pbval b s)"
  apply(induction a b rule: mk_dnf_conj.induct)
  apply(auto)
  done


lemma mk_dnf_is_nnf: "is_nnf a \<Longrightarrow>
           is_nnf b \<Longrightarrow>
           is_nnf (mk_dnf_conj  a  b)"
  apply(induction a b rule:  mk_dnf_conj.induct)
  apply(auto)
  done 


(* many counter examples occurs this way, TODO: make function for 'AND' *)
                                        
fun dnf_of_nnf :: "pbexp \<Rightarrow> pbexp" where            
"dnf_of_nnf (VAR x) = VAR x" |
"dnf_of_nnf (NOT y) = NOT y" |
"dnf_of_nnf (OR a b) = OR (dnf_of_nnf a) (dnf_of_nnf b)" |                                                       
"dnf_of_nnf (AND a b) =  mk_dnf_conj (dnf_of_nnf a) (dnf_of_nnf b)"                                                  
                                                  
lemma "pbval (dnf_of_nnf b) s = pbval b s"
  apply(induction b rule: dnf_of_nnf.induct )      
  apply(simp_all add: mk_dnf_preserv)                                           
  done                                             
                               
value "is_dnf(dnf_of_nnf(AND (OR (VAR []) (VAR [])) (OR (VAR []) (VAR []))))"

lemma mk_dnf_is_dnf: "is_dnf a \<Longrightarrow>
           is_dnf b \<Longrightarrow>
           is_dnf (mk_dnf_conj  a  b)"
  apply(induction a b rule:  mk_dnf_conj.induct)
  apply(auto)
  done 
                                  
lemma "is_nnf b \<Longrightarrow> is_dnf (dnf_of_nnf b)"     
  apply(induction b rule: dnf_of_nnf.induct)
  apply(auto simp add:  mk_dnf_is_dnf)                                                                                
  done                                      
end                                                    
