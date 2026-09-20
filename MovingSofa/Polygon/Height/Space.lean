import MovingSofa.Cap.Basic
import MovingSofa.Classical.Area

noncomputable section

namespace MovingSofa

def PolygonCapTranslateSpace (Θ : AngleSet) :=
  {S : Set Point // ∃ (K : PolygonCapSpace Θ) (q : Point),
    S = (fun p ↦ p + q) '' (K.val.val : Set Point)}

def PolygonHeightSpace (Θ : AngleSet) := angleDomain Θ → ℝ

def polygonHeightValue {Θ : AngleSet} (h : PolygonHeightSpace Θ) (t : ℝ) : ℝ := by
  classical
  exact if ht : t ∈ angleDomain Θ then h ⟨t, ht⟩ else 0

def polygonHeightParallelogram {Θ : AngleSet} (h : PolygonHeightSpace Θ) : Set Point :=
  ⋂ t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ),
    normalHalfPlane (t : Real.Angle) (polygonHeightValue h t) false false ∩
    normalHalfPlane (t : Real.Angle) (polygonHeightValue h t - 1) true false

def polygonHeightCap {Θ : AngleSet} (h : PolygonHeightSpace Θ) : Set Point :=
  polygonHeightParallelogram h ∩
    ⋂ t ∈ (Θ.directions : Set ℝ) ∪ ((fun t : ℝ ↦ t + Real.pi / 2) '' Θ.directions),
      normalHalfPlane (t : Real.Angle) (polygonHeightValue h t) false false

def polygonHeightFan {Θ : AngleSet} (h : PolygonHeightSpace Θ) : Set Point :=
  ⋂ t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ),
    normalHalfPlane (t : Real.Angle) (polygonHeightValue h t - 1) true false

def polygonHeightNiche {Θ : AngleSet} (h : PolygonHeightSpace Θ) : Set Point :=
  polygonHeightFan h ∩ ⋃ t ∈ Θ.directions,
    normalHalfPlane (t : Real.Angle) (polygonHeightValue h t - 1) false true ∩
    normalHalfPlane ((t + Real.pi / 2 : ℝ) : Real.Angle)
      (polygonHeightValue h (t + Real.pi / 2) - 1) false true

def polygonHeightArea {Θ : AngleSet} (h : PolygonHeightSpace Θ) : ℝ :=
  ClassicalResults.area (polygonHeightCap h) - ClassicalResults.area (polygonHeightNiche h)

def polygonHeightExtensions {Θ : AngleSet} (h : PolygonHeightSpace Θ) :
    Set Point × Set Point × Set Point × Set Point × ℝ :=
  (polygonHeightParallelogram h, polygonHeightCap h, polygonHeightFan h,
    polygonHeightNiche h, polygonHeightArea h)

def polygonTranslateHeight {Θ : AngleSet} (K : PolygonCapTranslateSpace Θ) :
    PolygonHeightSpace Θ := fun t ↦ supportValue K.val (t.val : Real.Angle)

def polygonTranslateExtensions {Θ : AngleSet} (K : PolygonCapTranslateSpace Θ) :
    Set Point × ℝ :=
  (polygonHeightNiche (polygonTranslateHeight K), polygonHeightArea (polygonTranslateHeight K))

end MovingSofa
