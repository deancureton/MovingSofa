import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section

open Filter Set
open scoped Topology

namespace MeasureTheory

/-- Moving interval cutoffs preserve almost-everywhere convergence on the limiting interior. -/
theorem ae_tendsto_indicator_Icc_of_tendsto_endpoints
    {E : Type*} [NormedAddCommGroup E] {a b : ℕ → ℝ} {c d : ℝ}
    {f : ℕ → ℝ → E} {g : ℝ → E}
    (ha : Tendsto a atTop (𝓝 c)) (hb : Tendsto b atTop (𝓝 d))
    (hf : ∀ᵐ x ∂volume, x ∈ Ioo c d → Tendsto (fun n ↦ f n x) atTop (𝓝 (g x))) :
    ∀ᵐ x ∂volume, Tendsto (fun n ↦ (Icc (a n) (b n)).indicator (f n) x)
      atTop (𝓝 ((Icc c d).indicator g x)) := by
  have hne (y : ℝ) : ∀ᵐ x ∂volume, x ≠ y := by
    simpa using (measure_eq_zero_iff_ae_notMem.mp (measure_singleton y :
      volume ({y} : Set ℝ) = 0))
  filter_upwards [hf, hne c, hne d] with x hx hxc hxd
  by_cases hmem : x ∈ Icc c d
  · have hxi : x ∈ Ioo c d :=
      ⟨lt_of_le_of_ne hmem.1 (Ne.symm hxc), lt_of_le_of_ne hmem.2 hxd⟩
    rw [indicator_of_mem hmem]
    apply (hx hxi).congr'
    filter_upwards [ha.eventually (gt_mem_nhds hxi.1),
      hb.eventually (lt_mem_nhds hxi.2)] with n hn hn'
    exact (indicator_of_mem (show x ∈ Icc (a n) (b n) from ⟨hn.le, hn'.le⟩) _).symm
  · rw [indicator_of_notMem hmem]
    apply tendsto_const_nhds.congr'
    have hout : x < c ∨ d < x := by
      simpa only [mem_Icc, not_and_or, not_le] using hmem
    rcases hout with hleft | hright
    · filter_upwards [ha.eventually (lt_mem_nhds hleft)] with n hn
      exact (indicator_of_notMem (show x ∉ Icc (a n) (b n) from
        fun h ↦ (not_le.mpr hn) h.1) _).symm
    · filter_upwards [hb.eventually (gt_mem_nhds hright)] with n hn
      exact (indicator_of_notMem (show x ∉ Icc (a n) (b n) from
        fun h ↦ (not_le.mpr hn) h.2) _).symm

/-- Dominated convergence on intervals whose endpoints converge, using convergence
only in the interior of the limiting interval. -/
theorem tendsto_integral_Icc_of_tendsto_endpoints
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {a b : ℕ → ℝ} {c d : ℝ} {f : ℕ → ℝ → E} {g : ℝ → E} {bound : ℝ → ℝ}
    (ha : Tendsto a atTop (𝓝 c)) (hb : Tendsto b atTop (𝓝 d))
    (hmeas : ∀ᶠ n in atTop, AEStronglyMeasurable (f n) (volume.restrict (Icc (a n) (b n))))
    (hbound : Integrable bound) (hbound_nonneg : ∀ᵐ x ∂volume, 0 ≤ bound x)
    (hdom : ∀ᶠ n in atTop, ∀ᵐ x ∂volume, x ∈ Icc (a n) (b n) → ‖f n x‖ ≤ bound x)
    (hf : ∀ᵐ x ∂volume, x ∈ Ioo c d → Tendsto (fun n ↦ f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n ↦ ∫ x in Icc (a n) (b n), f n x) atTop
      (𝓝 (∫ x in Icc c d, g x)) := by
  have hm : ∀ᶠ n in atTop,
      AEStronglyMeasurable ((Icc (a n) (b n)).indicator (f n)) volume := by
    filter_upwards [hmeas] with n hn
    exact (aestronglyMeasurable_indicator_iff measurableSet_Icc).mpr hn
  have hd : ∀ᶠ n in atTop, ∀ᵐ x ∂volume,
      ‖(Icc (a n) (b n)).indicator (f n) x‖ ≤ bound x := by
    filter_upwards [hdom] with n hn
    filter_upwards [hn, hbound_nonneg] with x hx hnonneg
    by_cases hmem : x ∈ Icc (a n) (b n)
    · simpa only [indicator_of_mem hmem] using hx hmem
    · simpa only [indicator_of_notMem hmem, norm_zero] using hnonneg
  have h := tendsto_integral_filter_of_dominated_convergence bound hm hd hbound
    (ae_tendsto_indicator_Icc_of_tendsto_endpoints ha hb hf)
  simpa only [integral_indicator measurableSet_Icc] using h

/-- A uniform bound on moving finite intervals suffices for dominated convergence. -/
theorem tendsto_integral_Icc_of_tendsto_endpoints_of_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {a b : ℕ → ℝ} {c d M : ℝ} {f : ℕ → ℝ → E} {g : ℝ → E}
    (ha : Tendsto a atTop (𝓝 c)) (hb : Tendsto b atTop (𝓝 d))
    (hmeas : ∀ᶠ n in atTop, AEStronglyMeasurable (f n) (volume.restrict (Icc (a n) (b n))))
    (hM : 0 ≤ M)
    (hdom : ∀ᶠ n in atTop, ∀ᵐ x ∂volume, x ∈ Icc (a n) (b n) → ‖f n x‖ ≤ M)
    (hf : ∀ᵐ x ∂volume, x ∈ Ioo c d → Tendsto (fun n ↦ f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n ↦ ∫ x in Icc (a n) (b n), f n x) atTop
      (𝓝 (∫ x in Icc c d, g x)) := by
  let s := Icc (c - 1) (d + 1)
  have hs : MeasurableSet s := measurableSet_Icc
  have hi : Integrable (s.indicator (fun _ : ℝ ↦ M)) volume := by
    apply IntegrableOn.integrable_indicator _ hs
    exact integrableOn_const isCompact_Icc.measure_lt_top.ne
  apply tendsto_integral_Icc_of_tendsto_endpoints ha hb hmeas hi
  · exact Eventually.of_forall fun x ↦ by
      by_cases hx : x ∈ s <;> simp [indicator, hx, hM]
  · filter_upwards [hdom, ha.eventually (lt_mem_nhds (show c - 1 < c by linarith)),
      hb.eventually (gt_mem_nhds (show d < d + 1 by linarith))] with n hn hna hnb
    filter_upwards [hn] with x hx
    intro hmem
    have hxs : x ∈ s := ⟨hna.le.trans hmem.1, hmem.2.trans hnb.le⟩
    simpa only [indicator_of_mem hxs] using hx hmem
  · exact hf

end MeasureTheory
