import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope

open Filter Set
open scoped Topology

namespace ConcaveOn

/-- A differentiable concave real function lies below its tangent line. -/
theorem le_add_deriv_mul_sub {s : Set ℝ} {g : ℝ → ℝ}
    (hg : ConcaveOn ℝ s g) {x : ℝ} (hx : x ∈ s)
    (hdiff : DifferentiableAt ℝ g x) {y : ℝ} (hy : y ∈ s) :
    g y ≤ g x + deriv g x * (y - x) := by
  rcases lt_trichotomy y x with hyx | rfl | hxy
  · have hslope := hg.deriv_le_slope hy hx hyx hdiff
    rw [slope] at hslope
    have hpos : 0 < x - y := sub_pos.mpr hyx
    have hs : deriv g x * (x - y) ≤ g x - g y := by
      apply (le_div_iff₀ hpos).mp
      simpa [smul_eq_mul, inv_mul_eq_div] using hslope
    nlinarith
  · simp
  · have hslope := hg.slope_le_of_hasDerivAt hx hy hxy hdiff.hasDerivAt
    rw [slope] at hslope
    have hpos : 0 < y - x := sub_pos.mpr hxy
    have hs : g y - g x ≤ deriv g x * (y - x) := by
      apply (div_le_iff₀ hpos).mp
      simpa [smul_eq_mul, inv_mul_eq_div] using hslope
    linarith


/-- Pointwise convergence of concave functions forces derivative convergence at a common
differentiability point in the interior of an interval. -/
theorem tendsto_deriv_of_tendsto_Ioo {ι : Type*} {F : Filter ι}
    {f : ι → ℝ → ℝ} {g : ℝ → ℝ}
    {a b x : ℝ} (hx : x ∈ Ioo a b)
    (hf : ∀ᶠ n in F, ConcaveOn ℝ (Ioo a b) (f n))
    (hlim : ∀ y ∈ Ioo a b, Tendsto (fun n ↦ f n y) F (𝓝 (g y)))
    (hdf : ∀ᶠ n in F, DifferentiableAt ℝ (f n) x)
    (hdg : DifferentiableAt ℝ g x) :
    Tendsto (fun n ↦ deriv (f n) x) F (𝓝 (deriv g x)) := by
  have hslope (y : ℝ) (hy : y ∈ Ioo a b) :
      Tendsto (fun n ↦ slope (f n) x y) F (𝓝 (slope g x y)) := by
    simpa only [slope, smul_eq_mul, vsub_eq_sub] using
      ((hlim y hy).sub (hlim x hx)).const_mul (y - x)⁻¹
  have hnear : ∀ᶠ y in 𝓝 x, y ∈ Ioo a b := isOpen_Ioo.mem_nhds hx
  apply tendsto_order.mpr
  constructor
  · intro l hl
    have hright := hdg.hasDerivAt.tendsto_slope.mono_left (nhdsGT_le_nhdsNE x)
    have hgood : ∀ᶠ y in 𝓝[>] x, y ∈ Ioo a b ∧ x < y ∧ l < slope g x y := by
      filter_upwards [hnear.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin,
        hright.eventually (lt_mem_nhds hl)] with y hy hxy hsy
      exact ⟨hy, hxy, hsy⟩
    obtain ⟨y, hy, hxy, hly⟩ := hgood.exists
    filter_upwards [hf, hdf, (hslope y hy).eventually (lt_mem_nhds hly)] with n hfn hdn hn
    exact hn.trans_le (hfn.slope_le_of_hasDerivAt hx hy hxy hdn.hasDerivAt)
  · intro u hu
    have hleft := hdg.hasDerivAt.tendsto_slope.mono_left (nhdsLT_le_nhdsNE x)
    have hgood : ∀ᶠ y in 𝓝[<] x, y ∈ Ioo a b ∧ y < x ∧ slope g x y < u := by
      filter_upwards [hnear.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin,
        hleft.eventually (gt_mem_nhds hu)] with y hy hyx hsy
      exact ⟨hy, hyx, hsy⟩
    obtain ⟨y, hy, hyx, hyu⟩ := hgood.exists
    filter_upwards [hf, hdf, (hslope y hy).eventually (gt_mem_nhds hyu)] with n hfn hdn hn
    have hle := hfn.deriv_le_slope hy hx hyx hdn
    rw [slope_comm] at hle
    exact hle.trans_lt hn

end ConcaveOn
