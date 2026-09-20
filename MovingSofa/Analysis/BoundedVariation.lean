import MovingSofa.Geometry.Basic
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

noncomputable section

namespace MovingSofa

/-- Bounded variation for a real function on its actual closed-interval domain. -/
def IsIntervalBoundedVariation (a b : ℝ) (f : Set.Icc a b → ℝ) : Prop :=
  BoundedVariationOn f Set.univ

private theorem intervalBV_add {a b : ℝ} {f g : Set.Icc a b → ℝ}
    (hf : IsIntervalBoundedVariation a b f) (hg : IsIntervalBoundedVariation a b g) :
    IsIntervalBoundedVariation a b (f + g) := by
  refine ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hf, hg⟩) ?_
  apply iSup_le
  rintro ⟨n, u, hu, hus⟩
  calc
    _ ≤ ∑ i ∈ Finset.range n,
        (edist (f (u (i + 1))) (f (u i)) + edist (g (u (i + 1))) (g (u i))) :=
      Finset.sum_le_sum fun _ _ ↦ edist_add_add_le _ _ _ _
    _ = _ := Finset.sum_add_distrib
    _ ≤ _ := add_le_add (eVariationOn.sum_le hu hus) (eVariationOn.sum_le hu hus)

/-- The submodule of continuous planar interval functions with coordinatewise finite variation. -/
def continuousBVSubmodule (a b : ℝ) : Submodule ℝ (Set.Icc a b → Point) where
  carrier := {f | Continuous f ∧
    ∀ i : Fin 2, IsIntervalBoundedVariation a b (fun t ↦ f t i)}
  zero_mem' := by
    refine ⟨continuous_const, fun i ↦ ?_⟩
    simp [IsIntervalBoundedVariation, BoundedVariationOn, eVariationOn]
  add_mem' := by
    intro f g hf hg
    exact ⟨hf.1.add hg.1, fun i ↦ intervalBV_add (hf.2 i) (hg.2 i)⟩
  smul_mem' := by
    intro c f hf
    refine ⟨continuous_const.smul hf.1, fun i ↦ ?_⟩
    exact (ContinuousLinearMap.lsmul ℝ ℝ c).lipschitzWith.comp_boundedVariationOn (hf.2 i)

/-- The real vector space of continuous planar BV paths on a closed interval. -/
abbrev ContinuousBVPaths (a b : ℝ) : Type := continuousBVSubmodule a b

/-- A continuous planar BV path has finite vector variation on its whole domain. -/
theorem ContinuousBVPaths.boundedVariationOn {a b : ℝ} (x : ContinuousBVPaths a b) :
    BoundedVariationOn x.val Set.univ := by
  have hdist (p q : Point) : edist p q ≤ edist (p 0) (q 0) + edist (p 1) (q 1) := by
    have hnorm (z : Point) : ‖z‖ ≤ |z 0| + |z 1| := by
      nlinarith [Point.norm_sq_eq z, sq_abs (z 0), sq_abs (z 1), abs_nonneg (z 0),
        abs_nonneg (z 1), norm_nonneg z, mul_nonneg (abs_nonneg (z 0)) (abs_nonneg (z 1))]
    simp only [edist_dist, dist_eq_norm, Real.norm_eq_abs]
    rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (by simpa using hnorm (p - q))
  refine ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨x.property.2 0, x.property.2 1⟩) ?_
  apply iSup_le
  rintro ⟨n, u, hu, hus⟩
  calc
    _ ≤ ∑ i ∈ Finset.range n,
        (edist (x.val (u (i + 1)) 0) (x.val (u i) 0) +
          edist (x.val (u (i + 1)) 1) (x.val (u i) 1)) :=
      Finset.sum_le_sum fun _ _ ↦ hdist _ _
    _ = _ := Finset.sum_add_distrib
    _ ≤ _ := add_le_add (eVariationOn.sum_le (f := fun t ↦ x.val t 0) (n := n) hu hus)
      (eVariationOn.sum_le (f := fun t ↦ x.val t 1) (n := n) hu hus)

end MovingSofa
