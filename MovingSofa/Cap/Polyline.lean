import MovingSofa.Cap.PolylineDefinition

noncomputable section

namespace MovingSofa

def polygonCapPolyline {Θ : AngleSet} (K : PolygonCapSpace Θ) : XMonotonePolylineData :=
  (polygonCap_polyline K).choose

def polygonCapPolylineLength {Θ : AngleSet} (K : PolygonCapSpace Θ)
    (t : angleDomain Θ) : ℝ := by
  classical
  let p := polygonCapPolyline K
  exact ∑ i : Fin p.edges,
    if inner ℝ (p.vertices i.succ - p.vertices i.castSucc)
      (normalVector (t.val : Real.Angle)) = 0 then
      dist (p.vertices i.castSucc) (p.vertices i.succ) else 0

def IsBalancedPolygonCap {Θ : AngleSet} (K : PolygonCapSpace Θ) : Prop :=
  ∀ t : angleDomain Θ, surfaceAreaMeasure K.val.val {(t.val : Real.Angle)} =
    ENNReal.ofReal (polygonCapPolylineLength K t)

end MovingSofa
