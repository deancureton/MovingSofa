import MovingSofa.Polygon.Height.Space

noncomputable section

namespace MovingSofa

/-- Increase one selected support height by the prescribed amount. -/
def raisedPolygonSupport {Θ : AngleSet} (K : PolygonCapSpace Θ)
    (t : angleDomain Θ) (ε : ℝ) : PolygonHeightSpace Θ := by
  classical
  exact fun s ↦ supportValue (K.val.val : Set Point) (s.val : Real.Angle) +
    if s = t then ε else 0

end MovingSofa
