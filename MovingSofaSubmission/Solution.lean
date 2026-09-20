import MovingSofa.Optimality
import MovingSofa.Motion.CanonicalUpperBound
import MovingSofa.External

/-!
# The moving sofa problem: proofs

Proves the three statements of `MovingSofaSubmission.Challenge`. Two of them are proved in
earlier files and are available here by import: `MovingSofa.GerversSofa.ABφθSpec.existsUnique`
in `MovingSofa.Canonical.Definitions`, and `MovingSofa.isMovingSofa_gerversSofa` in
`MovingSofa.Gerver.Motion`. The main theorem follows from
the area upper bound `MovingSofa.areaUpperBound`.
-/

namespace MovingSofa

open MeasureTheory

/-- Gerver's sofa attains the sofa constant (Baek, arXiv:2411.19826). -/
theorem sofaConstant_eq_volume_gerversSofa : sofaConstant = volume gerversSofa := by
  apply optimality_of_areaUpperBound
  exact areaUpperBound

end MovingSofa
