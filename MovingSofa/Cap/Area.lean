import MovingSofa.Cap.Basic
import MovingSofa.Classical.Area

noncomputable section

namespace MovingSofa

/-- Cap area minus niche area, with real Lebesgue area as in the classical interface. -/
def capAreaFunctional {ω : ℝ} (K : CapSpace ω) : ℝ :=
  ClassicalResults.area (K.1 : Set Point) - ClassicalResults.area (capNiche K)

/-- The cap space at a right angle. -/
abbrev RightAngleCapSpace := CapSpace (Real.pi / 2)

/-- The sofa area functional on the right-angle cap space. -/
def rightAngleAreaFunctional (K : RightAngleCapSpace) : ℝ := capAreaFunctional K

end MovingSofa
