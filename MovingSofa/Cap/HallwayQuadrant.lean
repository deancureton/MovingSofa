import MovingSofa.Cap.Basic
import MovingSofa.Geometry.HallwayPartsProperties

noncomputable section

namespace MovingSofa

/-- The inward quadrant of the supporting hallway at angle `t` is the inward quadrant of `s`
written in support-value coordinates. -/
theorem rotatingHallwayParts_innerQuadrant (s : Set Point) (t : ℝ) :
    (rotatingHallwayParts s (t : Real.Angle)).innerQuadrant = innerQuadrant s t := by
  rw [(rotatingHallwayParts_formulas s (t : Real.Angle)).2.2.2.2.2.2.2.2]
  simp only [innerQuadrant, Real.Angle.coe_add]

end MovingSofa
