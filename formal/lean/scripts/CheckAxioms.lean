import ThomsonN9.Solution
/-! Axiom check for all four proved challenge theorems (`thomson_nine_M0`, `thomson_nine_M1`,
    `thomson_nine`, `thomson_nine_unique`) together with the ported admissibility lemmas.
    Every declaration must depend only on `propext`, `Classical.choice` and `Quot.sound`
    (in particular no `sorryAx`, `ofReduceBool`, `ofReduceNat` or `trustCompiler`). -/
#print axioms ThomsonN9.thomson_nine_M0
#print axioms ThomsonN9.thomson_nine_M1
#print axioms ThomsonN9.thomson_nine
#print axioms ThomsonN9.thomson_nine_unique
#print axioms ThomsonN9.thomson_nine_main
#print axioms ThomsonN9.triCapPrism_injective
#print axioms ThomsonN9.triCapPrism_mem
#check @ThomsonN9.thomson_nine_M0
#check @ThomsonN9.thomson_nine_M1
#check @ThomsonN9.thomson_nine
#check @ThomsonN9.thomson_nine_unique
#check @ThomsonN9.thomson_nine_main
