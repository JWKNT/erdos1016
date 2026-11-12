import Erdos1016.ExactMaximum.Main

#print axioms Erdos1016.ExactMaximum.gapStatement
#print axioms Erdos1016.ExactMaximum.fourCutStatement
#print axioms Erdos1016.ExactMaximum.upperBoundStatement
#print axioms Erdos1016.ExactMaximum.exactMaximumStatement
#print axioms Erdos1016.ExactMaximum.exactMaximum
#print axioms Erdos1016.ExactMaximum.maxCycles_parity
#print axioms Erdos1016.ExactMaximum.maxCycles_formula
#print axioms Erdos1016.ExactMaximum.maxCycles_secondOrder
#print axioms Erdos1016.ExactMaximum.maxCycles_secondOrder_explicit
#print axioms Erdos1016.ExactMaximum.parity_of_exactMaximum
#print axioms Erdos1016.ExactMaximum.formula_of_exactMaximum
#print axioms Erdos1016.ExactMaximum.secondOrder_of_exactMaximum
#print axioms Erdos1016.ExactMaximum.secondOrder_explicit_of_exactMaximum
#print axioms Erdos1016.mainTheorem
#print axioms Erdos1016.cycleCountTheorem

example : Erdos1016.ExactMaximum.ExactMaximumStatement :=
  Erdos1016.ExactMaximum.exactMaximumStatement
example : Erdos1016.ExactMaximumSupport.SharpSecondOrderStatement :=
  Erdos1016.ExactMaximumSupport.sharpSecondOrder_of_exactMaximum
    Erdos1016.ExactMaximum.exactMaximumStatement

#check Erdos1016.ExactMaximum.exactMaximum
#check Erdos1016.ExactMaximum.maxCycles_parity
#check Erdos1016.ExactMaximum.maxCycles_formula
#check Erdos1016.ExactMaximum.maxCycles_secondOrder
#check Erdos1016.ExactMaximum.maxCycles_secondOrder_explicit
