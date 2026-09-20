import MovingSofa.ForMathlib.Topology.Order.Interval
import MovingSofa.Analysis.BoundedVariation
import Mathlib.MeasureTheory.VectorMeasure.BoundedVariation
import Mathlib.MeasureTheory.VectorMeasure.SetIntegral

noncomputable section

open MeasureTheory

namespace MovingSofa

/-- A right-continuous real BV function on its actual closed-interval domain. -/
structure RightContinuousIntervalBV (a b : ℝ) where
  toFun : Set.Icc a b → ℝ
  boundedVariation : IsIntervalBoundedVariation a b toFun
  right_continuous : ∀ t, ContinuousWithinAt toFun (Set.Ici t) t

/-- A right-continuous interval-BV function is determined by its underlying function. -/
theorem RightContinuousIntervalBV.toFun_injective {a b : ℝ} :
    Function.Injective (@RightContinuousIntervalBV.toFun a b) := by
  rintro ⟨f, hf, hfr⟩ ⟨g, hg, hgr⟩ hfg
  cases hfg
  rfl

/-- A right-continuous interval-BV function on a nonempty interval is bounded, by its value at
the left endpoint plus the total variation. -/
theorem RightContinuousIntervalBV.exists_norm_bound {a b : ℝ} (hab : a ≤ b)
    (f : RightContinuousIntervalBV a b) : ∃ C : ℝ, ∀ t, ‖f.toFun t‖ ≤ C := by
  refine ⟨‖f.toFun ⟨a, le_rfl, hab⟩‖ + (eVariationOn f.toFun Set.univ).toReal, fun t ↦ ?_⟩
  calc ‖f.toFun t‖
      ≤ ‖f.toFun ⟨a, le_rfl, hab⟩‖ + ‖f.toFun t - f.toFun ⟨a, le_rfl, hab⟩‖ :=
        norm_le_norm_add_norm_sub' _ _
    _ ≤ _ := by
        gcongr
        simpa [dist_eq_norm_sub] using
          f.boundedVariation.dist_le (Set.mem_univ t) (Set.mem_univ ⟨a, le_rfl, hab⟩)

/-- The finite signed Stieltjes measure on the interval, with zero initial atom. -/
def intervalStieltjesMeasure {a b : ℝ} (f : RightContinuousIntervalBV a b) :
    SignedMeasure (Set.Icc a b) :=
  f.boundedVariation.vectorMeasure

/-- The Stieltjes integral, used for bounded measurable integrands and Borel subsets. -/
def intervalStieltjesIntegral {a b : ℝ} (f : RightContinuousIntervalBV a b)
    (g : Set.Icc a b → ℝ) (X : Set (Set.Icc a b)) : ℝ :=
  ∫ᵛ t in X, g t ∂[ContinuousLinearMap.mul ℝ ℝ; intervalStieltjesMeasure f]

/-- Over the whole parameter interval, the interval Stieltjes integral is the unrestricted
vector-measure integral. -/
theorem intervalStieltjesIntegral_univ {a b : ℝ} (f : RightContinuousIntervalBV a b)
    (g : Set.Icc a b → ℝ) :
    intervalStieltjesIntegral f g Set.univ =
      VectorMeasure.integral (intervalStieltjesMeasure f) g (ContinuousLinearMap.mul ℝ ℝ) := by
  simp only [intervalStieltjesIntegral, VectorMeasure.restrict_univ]

end MovingSofa
