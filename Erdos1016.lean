import Erdos1016.Main
import Erdos1016.PolynomialBound.Statement
import Erdos1016.PolynomialBound.LinkBound
import Erdos1016.PolynomialBound.TwoLinkMoment
import Erdos1016.PolynomialBound.Chain
import Erdos1016.PolynomialBound.Product

/-!
# Erdős problem 1016

The few-component-witness proof, with unconditional endpoint
`Erdos1016.mainTheorem : Problem1016.MainTheorem` and the equivalent
integer-excess statement. The same forest estimate gives the cycle-count
endpoints `Erdos1016.cycleCountTheorem` and `Erdos1016.cycleCountAsymptotic`.
Two elementary theorems on paths and cycles, `Erdos1016.twoTerminalTheorem` and
`Erdos1016.noWasteTheorem`, do not use the forest estimate.
The modules under `Erdos1016/PolynomialBound/` prove steps of two results that
are not formalized as a whole: the bound `2^(r-1) + K r 2^(r/2)` for the number
of cycles, and the forest estimate with a polynomial error. They contain no
endpoint theorem.
The previous formalization and its manuscript are preserved separately under
`old/` and are not imported.
-/
