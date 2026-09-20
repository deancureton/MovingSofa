import MovingSofa.Analysis.SurfaceMeasure.Basic
import MovingSofa.Cap.Area
import MovingSofa.Geometry.Hallway
import MovingSofa.Gerver.Parameters

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal

namespace MovingSofa

/-- The real-angle inner-corner path of a cap. -/
def capInnerCorner (K : RightAngleCapSpace) (t : ℝ) : Point :=
  (rotatingHallwayParts (K.1 : Set Point) (t : Real.Angle)).innerCorner

/-- The two surface densities on the upper half-circle, with the top atom excluded. -/
def HasCapDensities (K : RightAngleCapSpace) (r s : ℝ → ℝ≥0) : Prop :=
  Measurable r ∧ Measurable s ∧
    (surfaceAreaMeasure K.1).restrict
        ((fun t : ℝ ↦ (t : Real.Angle)) '' Set.Ico 0 (Real.pi / 2)) =
      Measure.map (fun t : ℝ ↦ (t : Real.Angle))
        ((volume.restrict (Set.Ico 0 (Real.pi / 2))).withDensity (fun t ↦ (r t : ℝ≥0∞))) ∧
    (surfaceAreaMeasure K.1).restrict
        ((fun t : ℝ ↦ (t : Real.Angle)) '' Set.Ioc (Real.pi / 2) Real.pi) =
      Measure.map (fun t : ℝ ↦ ((t + Real.pi / 2 : ℝ) : Real.Angle))
        ((volume.restrict (Set.Ioc 0 (Real.pi / 2))).withDensity (fun t ↦ (s t : ℝ≥0∞)))

/-- The density, corner regularity and strict interior signs of the injectivity condition. -/
def SatisfiesInjectivityCondition (K : RightAngleCapSpace) : Prop :=
  (∃ r s : ℝ → ℝ≥0, HasCapDensities K r s ∧
    ∀ r' s', HasCapDensities K r' s' →
      (r =ᵐ[volume.restrict (Set.Icc 0 (Real.pi / 2))] r') ∧
      (s =ᵐ[volume.restrict (Set.Icc 0 (Real.pi / 2))] s')) ∧
    ContDiffOn ℝ 1 (capInnerCorner K) (Set.Icc 0 (Real.pi / 2)) ∧
    ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      inner ℝ (derivWithin (capInnerCorner K) (Set.Icc 0 (Real.pi / 2)) t)
        (normalVector (t : Real.Angle)) < 0 ∧
      0 < inner ℝ (derivWithin (capInnerCorner K) (Set.Icc 0 (Real.pi / 2)) t)
        (tangentVector (t : Real.Angle))

/-- Right-angle caps satisfying injectivity and the cap-area threshold. -/
def SpecialCapSpace :=
  {K : RightAngleCapSpace // SatisfiesInjectivityCondition K ∧
    (11 : ℝ) / 5 ≤ ClassicalResults.area (K.1 : Set Point)}

/-- A special cap and two convex tails satisfying the support constraints. -/
structure CapTailSpace where
  cap : SpecialCapSpace
  rightBody : ConvexBody Point
  leftBody : ConvexBody Point
  right_subset : (rightBody : Set Point) ⊆ (cap.1.1 : Set Point)
  left_subset : (leftBody : Set Point) ⊆ (cap.1.1 : Set Point)
  right_bound : ∀ t ∈ Set.Icc paperGerverConstants.2.1 (Real.pi / 2),
    supportValue cap.1.1 (t : Real.Angle) +
      supportValue rightBody ((Real.pi + t : ℝ) : Real.Angle) ≤ 1
  right_eq : ∀ t ∈ ({paperGerverConstants.2.1, Real.pi / 2} : Set ℝ),
    supportValue cap.1.1 (t : Real.Angle) +
      supportValue rightBody ((Real.pi + t : ℝ) : Real.Angle) = 1
  left_bound : ∀ t ∈ Set.Icc (0 : ℝ) paperGerverConstants.2.2,
    supportValue cap.1.1 ((Real.pi / 2 + t : ℝ) : Real.Angle) +
      supportValue leftBody ((3 * Real.pi / 2 + t : ℝ) : Real.Angle) ≤ 1
  left_eq : ∀ t ∈ ({0, paperGerverConstants.2.2} : Set ℝ),
    supportValue cap.1.1 ((Real.pi / 2 + t : ℝ) : Real.Angle) +
      supportValue leftBody ((3 * Real.pi / 2 + t : ℝ) : Real.Angle) = 1

end MovingSofa
