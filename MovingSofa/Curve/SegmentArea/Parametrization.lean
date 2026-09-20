import MovingSofa.Analysis.Stieltjes.Affine
import MovingSofa.Curve.Jordan.Area
import MovingSofa.Curve.SegmentArea

noncomputable section

namespace MovingSofa

open MeasureTheory Set

def lineSegmentBVPath (p q : Point) : ContinuousBVPaths 0 1 where
  val := Path.segment p q
  property := by
    constructor
    · exact (Path.segment p q).continuous
    · intro i
      let C : NNReal := ⟨|q i - p i|, abs_nonneg _⟩
      have hLip : LipschitzWith C (fun r : ℝ ↦ p i + r * (q i - p i)) := by
        apply LipschitzWith.of_dist_le_mul
        intro x y
        simp only [Real.dist_eq]
        change |(p i + x * (q i - p i)) - (p i + y * (q i - p i))| ≤
          |q i - p i| * |x - y|
        rw [show (p i + x * (q i - p i)) - (p i + y * (q i - p i)) =
          (x - y) * (q i - p i) by ring, abs_mul, mul_comm]
      have hid : BoundedVariationOn ((↑) : Set.Icc (0 : ℝ) 1 → ℝ) Set.univ := by
        apply ((show Monotone ((↑) : Set.Icc (0 : ℝ) 1 → ℝ) from fun _ _ h ↦ h).monotoneOn
          Set.univ).boundedVariationOn (C := 1)
        intro t _
        rw [abs_of_nonneg t.property.1]
        exact t.property.2
      have hbv := hLip.comp_boundedVariationOn hid
      rw [show (fun t ↦ (Path.segment p q t) i) =
          (fun r : ℝ ↦ p i + r * (q i - p i)) ∘ ((↑) : Set.Icc (0 : ℝ) 1 → ℝ) by
        funext t
        simp [Function.comp_apply, Path.segment_apply, AffineMap.lineMap_apply_module']
        change (t : ℝ) * (q i - p i) + p i =
          p i + (t : ℝ) * (q i - p i)
        ring]
      exact hbv

/-- The affine parametrization of an oriented segment, evaluated. -/
theorem lineSegmentBVPath_apply (p q : Point) (s : Set.Icc (0 : ℝ) 1) :
    (lineSegmentBVPath p q).val s = (1 - (s : ℝ)) • p + (s : ℝ) • q := by
  show Path.segment p q s = _
  simp [Path.segment_apply, AffineMap.lineMap_apply_module']
  module

theorem curveAreaFunctional_lineSegmentBVPath (p q : Point) :
    curveAreaFunctional (lineSegmentBVPath p q) = segmentArea p q := by
  have hcoord (i : Fin 2) (t : Set.Icc (0 : ℝ) 1) :
      (continuousBVCoordinate (lineSegmentBVPath p q) i).toFun t =
        p i + (q i - p i) * (t : ℝ) := by
    change (Path.segment p q t) i = _
    simp [Path.segment_apply, AffineMap.lineMap_apply_module']
    ring
  unfold curveAreaFunctional segmentArea
  change
    (intervalStieltjesIntegral
        (continuousBVCoordinate (lineSegmentBVPath p q) 1)
        (continuousBVCoordinate (lineSegmentBVPath p q) 0).toFun Set.univ -
      intervalStieltjesIntegral
        (continuousBVCoordinate (lineSegmentBVPath p q) 0)
        (continuousBVCoordinate (lineSegmentBVPath p q) 1).toFun Set.univ) / 2 =
      planeCrossProduct p q / 2
  rw [intervalStieltjesIntegral_affine_cross
    (continuousBVCoordinate (lineSegmentBVPath p q) 0)
    (continuousBVCoordinate (lineSegmentBVPath p q) 1)
    (p 0) (q 0 - p 0) (p 1) (q 1 - p 1) (hcoord 0) (hcoord 1)]
  simp only [planeCrossProduct]
  ring

end MovingSofa
