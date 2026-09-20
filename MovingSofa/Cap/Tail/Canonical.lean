import MovingSofa.Cap.Tail.Space

noncomputable section

namespace MovingSofa

/-- The closed half-planes above the right and left inner supporting walls. -/
def innerWallUpperHalfPlanes (K : RightAngleCapSpace) (t : ℝ) : Set Point × Set Point :=
  (normalHalfPlane (t : Real.Angle) (supportValue K.1 (t : Real.Angle) - 1) true false,
    normalHalfPlane ((t + Real.pi / 2 : ℝ) : Real.Angle)
      (supportValue K.1 ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1) true false)

/-- The right and left canonical tail sets, before bundling their convex-body proofs. -/
def canonicalTailSets (K : SpecialCapSpace) : Set Point × Set Point :=
  ((K.1.1 : Set Point) ∩
      ⋂ t ∈ Set.Icc paperGerverConstants.2.1 (Real.pi / 2),
        (innerWallUpperHalfPlanes K.1 t).1,
    (K.1.1 : Set Point) ∩
      ⋂ t ∈ Set.Icc (0 : ℝ) paperGerverConstants.2.2,
        (innerWallUpperHalfPlanes K.1 t).2)

end MovingSofa
