theory ConcreteSemantics12_VCG
  imports "~~/src/HOL/IMP/Hoare"
begin

subsection "Verification Condition Generation"

subsubsection "Annotated Commands"

text\<open>Commands where loops are annotated with invariants.\<close>

datatype acom = 
Askip ("SKIP")|
Aassign vname aexp ("(_ ::= _)" [1000,61] 61)|
Aseq acom acom ("(_;;/ _)" [60,61]60)|
Aif bexp acom acom ("(IF _/ THEN _/ ELSE _)" [0, 0, 61] 61)|
Awhile assn bexp com ("({_}/ WHILE _/ DO _) [0, 0, 61] 61")

notation com.SKIP ("SKIP")

end