import MovingSofa.Convex.ArcArea

noncomputable section

namespace MovingSofa

def mamikonFunctional (K : ConvexBody Point) (a b : ℝ)
    (hab : a < b) (_hba : b < a + Real.pi) (z : ContinuousBVPaths a b)
    (_hz : ∀ t : Set.Icc a b,
      z.val t ∈ (supportingLineHalfPlane K (t.val : Real.Angle)).1) : ℝ :=
  segmentArea (edgeVertices K (a : Real.Angle)).1
      (z.val ⟨a, le_rfl, hab.le⟩) +
    curveAreaFunctional z +
    segmentArea (z.val ⟨b, hab.le, le_rfl⟩)
      (edgeVertices K (b : Real.Angle)).2 -
    convexArcArea K a b

end MovingSofa
