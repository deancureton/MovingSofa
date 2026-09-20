import MovingSofa.Analysis.Stieltjes.RiemannSums
import MovingSofa.Curve.Area
import MovingSofa.ForMathlib.BoundedVariation

/-!
# A Stieltjes chain rule with a local quadratic remainder

The hypothesis of `ContinuousBVPaths.stieltjes_chain_rule_of_local_quadratic_remainder`
quantifies the remainder only over parameter pairs closer than a fixed positive threshold.
This is what a locally defined argument branch supplies: no single plane function has to be
named, and no constant is needed across a branch cut.
-/

noncomputable section

open Set

namespace MovingSofa

/-- If a real parameter function `A` has increments matching the signed pair
`D₁ dγ₁ - D₀ dγ₀` up to a quadratic remainder on all parameter pairs closer than a fixed
positive threshold, then its endpoint increment is the corresponding difference of
coordinate Stieltjes integrals. -/
theorem ContinuousBVPaths.stieltjes_chain_rule_of_local_quadratic_remainder
    {a b : ℝ} (hab : a ≤ b) (x : ContinuousBVPaths a b)
    (hBV : BoundedVariationOn x.val univ) (A : Set.Icc a b → ℝ) (D : Point → Fin 2 → ℝ)
    (hD : ∀ i, Continuous (fun t ↦ D (x.val t) i)) {C : ℝ} (hC : 0 ≤ C)
    {δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    (herror : ∀ t u : Set.Icc a b, (t : ℝ) ≤ (u : ℝ) → (u : ℝ) - (t : ℝ) < δ₀ →
      |A u - A t -
        (D (x.val t) 1 * (x.val u 1 - x.val t 1) -
          D (x.val t) 0 * (x.val u 0 - x.val t 0))| ≤ C * ‖x.val u - x.val t‖ ^ 2) :
    A ⟨b, hab, le_rfl⟩ - A ⟨a, le_rfl, hab⟩ =
      intervalStieltjesIntegral (continuousBVCoordinate x 1) (fun t ↦ D (x.val t) 1) univ -
      intervalStieltjesIntegral (continuousBVCoordinate x 0) (fun t ↦ D (x.val t) 0) univ := by
  obtain ⟨cuts, hcuts, hzero, hlast, hmesh⟩ :=
    Set.Icc.exists_partitions_mesh_tendsto_zero hab
  let N : ℕ → ℕ := fun k ↦ k + 1
  have htaylor := hBV.tendsto_sum_of_local_quadratic_remainder hab x.property.1 A
    (fun t v ↦ D (x.val t) 1 * v 1 - D (x.val t) 0 * v 0) hC hδ₀ herror
    N cuts hcuts hzero hlast hmesh
  have hcoord (i : Fin 2) := tendsto_stieltjesSum_of_mesh_tendsto_zero
    (continuousBVCoordinate x i) ((PiLp.continuous_apply 2 _ i).comp x.property.1)
    (hD i) N cuts hcuts hzero hlast hmesh
  have hsum := (hcoord 1).sub (hcoord 0)
  simp only [← Finset.sum_sub_distrib, continuousBVCoordinate] at hsum
  exact tendsto_nhds_unique htaylor hsum

end MovingSofa
