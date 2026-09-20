import MovingSofa.Cap.Polyline

noncomputable section

namespace MovingSofa

def polygonPolylineLengthAt {Θ : AngleSet} (K : PolygonCapSpace Θ) (t : ℝ) : ℝ := by
  classical
  exact if ht : t ∈ angleDomain Θ then polygonCapPolylineLength K ⟨t, ht⟩ else 0

def nicheBoundaryLength {Θ : AngleSet} (K : PolygonCapSpace Θ) (S : Set Point) : ℝ :=
  (MeasureTheory.Measure.hausdorffMeasure 1 (frontier (polygonNiche Θ K.val) ∩ S)).toReal

end MovingSofa
