import MovingSofa.Geometry.Basic
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Map

noncomputable section

open MeasureTheory

namespace MovingSofa

instance angleMeasurableSpace : MeasurableSpace Real.Angle := borel Real.Angle

instance angleBorelSpace : BorelSpace Real.Angle := ⟨rfl⟩

/-- An exterior normal direction at a point of a convex body. -/
def IsExteriorNormal (K : ConvexBody Point) (p : Point) (a : Real.Angle) : Prop :=
  ∀ q ∈ (K : Set Point), inner ℝ (q - p) (normalVector a) ≤ 0

/-- Boundary points with exactly one exterior unit normal. -/
def regularBoundary (K : ConvexBody Point) : Set Point :=
  {p | p ∈ frontier (K : Set Point) ∧ ∃! a, IsExteriorNormal K p a}

/-- The unique exterior normal at regular points, extended by zero elsewhere. -/
def exteriorNormalAngle (K : ConvexBody Point) (p : Point) : Real.Angle := by
  classical
  exact if h : ∃! a, IsExteriorNormal K p a then h.exists.choose else 0

/-- A nontrivial segment presentation and a perpendicular angular direction. -/
def IsSegmentPresentation (K : ConvexBody Point) (d : Point × Point × Real.Angle) : Prop :=
  d.1 ≠ d.2.1 ∧ (K : Set Point) = segment ℝ d.1 d.2.1 ∧
    inner ℝ (d.2.1 - d.1) (normalVector d.2.2) = 0

/-- Surface measure in angular coordinates, including point and segment bodies. -/
def surfaceAreaMeasure (K : ConvexBody Point) : Measure Real.Angle := by
  classical
  exact if (K : Set Point).Subsingleton then 0
  else if h : ∃ d, IsSegmentPresentation K d then
    let d := h.choose
    ENNReal.ofReal (dist d.1 d.2.1) •
      (Measure.dirac d.2.2 + Measure.dirac (d.2.2 + ((Real.pi : ℝ) : Real.Angle)))
  else
    Measure.map (exteriorNormalAngle K)
      ((Measure.hausdorffMeasure 1).restrict (regularBoundary K))

end MovingSofa
