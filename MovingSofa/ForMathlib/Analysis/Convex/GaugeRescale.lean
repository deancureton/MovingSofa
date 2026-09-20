import MovingSofa.ForMathlib.Analysis.Convex.Gauge
import Mathlib.Analysis.Convex.GaugeRescale

open Set
open scoped Topology NNReal Pointwise

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Gauge rescaling identifies the unit sphere with the frontier of a bounded convex neighborhood. -/
noncomputable def radialGaugeHomeomorph [Nontrivial E] {s : Set E}
    (hs : Convex ℝ s) (h₀ : s ∈ nhds (0 : E))
    (hb : Bornology.IsVonNBounded ℝ s) :
    {u : E | ‖u‖ = 1} ≃ₜ ↥(frontier s) := by
  let e := gaugeRescaleHomeomorph (Metric.ball (0 : E) 1) s
    (convex_ball 0 1) (Metric.ball_mem_nhds _ (by norm_num))
    (NormedSpace.isVonNBounded_ball ℝ E 1) hs h₀ hb
  have he : e '' frontier (Metric.ball (0 : E) 1) = frontier s := by
    rw [← closure_sdiff_interior, Set.image_sdiff e.injective]
    rw [image_gaugeRescaleHomeomorph_closure, image_gaugeRescaleHomeomorph_interior]
    exact closure_sdiff_interior s
  have hunit : {u : E | ‖u‖ = 1} = frontier (Metric.ball (0 : E) 1) := by
    rw [frontier_ball _ one_ne_zero]
    ext u
    simp
  exact (Homeomorph.setCongr hunit).trans ((e.image _).trans (Homeomorph.setCongr he))

/-- The radial gauge homeomorphism sends a unit vector to its reciprocal-gauge multiple. -/
lemma radialGaugeHomeomorph_apply [Nontrivial E] {s : Set E}
    (hs : Convex ℝ s) (h₀ : s ∈ nhds (0 : E))
    (hb : Bornology.IsVonNBounded ℝ s) (u : {u : E | ‖u‖ = 1}) :
    (radialGaugeHomeomorph hs h₀ hb u : E) = (gauge s u.val)⁻¹ • u.val := by
  change (gauge (Metric.ball (0 : E) 1) u.val / gauge s u.val) • u.val = _
  rw [gauge_ball (by norm_num), div_one]
  have hu : ‖u.val‖ = 1 := u.property
  rw [hu, one_div]


open scoped Pointwise

/-- Translate the radial gauge homeomorphism by a fixed vector. -/
noncomputable def translatedRadialGaugeHomeomorph [Nontrivial E] {s : Set E}
    (hs : Convex ℝ s) (h₀ : s ∈ nhds (0 : E))
    (hb : Bornology.IsVonNBounded ℝ s) (o : E) :
    {u : E | ‖u‖ = 1} ≃ₜ ↥(frontier (o +ᵥ s)) := by
  let e : E ≃ₜ E := Homeomorph.addLeft o
  have he : e '' frontier s = frontier (o +ᵥ s) := by
    rw [e.image_frontier]
    rfl
  exact (radialGaugeHomeomorph hs h₀ hb).trans
    ((e.image _).trans (Homeomorph.setCongr he))

/-- The translated radial gauge homeomorphism has the expected affine formula. -/
lemma translatedRadialGaugeHomeomorph_apply [Nontrivial E] {s : Set E}
    (hs : Convex ℝ s) (h₀ : s ∈ nhds (0 : E))
    (hb : Bornology.IsVonNBounded ℝ s) (o : E) (u : {u : E | ‖u‖ = 1}) :
    (translatedRadialGaugeHomeomorph hs h₀ hb o u : E) =
      o + (gauge s u.val)⁻¹ • u.val := by
  change o + (radialGaugeHomeomorph hs h₀ hb u : E) = _
  rw [radialGaugeHomeomorph_apply]

/-- The translated radial gauge homeomorphism is Lipschitz on the unit sphere. -/
lemma exists_lipschitzWith_translatedRadialGaugeHomeomorph [Nontrivial E] {s : Set E}
    (hs : Convex ℝ s) (h₀ : s ∈ nhds (0 : E))
    (hb : Bornology.IsVonNBounded ℝ s) (o : E) {R : ℝ} (hR : 0 < R)
    (hbound : s ⊆ Metric.closedBall 0 R) :
    ∃ C, LipschitzWith C (fun u ↦ (translatedRadialGaugeHomeomorph hs h₀ hb o u : E)) := by
  obtain ⟨C, hC⟩ := hs.exists_lipschitzWith_radial_gauge_sphere h₀ hR hbound
  refine ⟨C, LipschitzWith.of_dist_le_mul fun u v ↦ ?_⟩
  rw [translatedRadialGaugeHomeomorph_apply, translatedRadialGaugeHomeomorph_apply,
    dist_add_left]
  exact hC.dist_le_mul u v

/-- A bounded convex set with an interior basepoint admits a positive Lipschitz radial parametrization of its frontier. -/
lemma exists_radial_homeomorph [Nontrivial E] {s : Set E}
    (hs : Convex ℝ s) (hb : Bornology.IsBounded s) (o : E) (ho : o ∈ interior s) :
    ∃ (ρ : E → ℝ) (e : {u : E | ‖u‖ = 1} ≃ₜ ↥(frontier s)) (C : NNReal),
      (∀ u, ‖u‖ = 1 → 0 < ρ u ∧ o + ρ u • u ∈ frontier s ∧
        ∀ r : ℝ, 0 < r → o + r • u ∈ frontier s → r = ρ u) ∧
      (∀ u, (e u : E) = o + ρ u.val • u.val) ∧
      LipschitzWith C (fun u ↦ (e u : E)) := by
  let t : Set E := -o +ᵥ s
  have htconv : Convex ℝ t := hs.vadd (-o)
  have htzero : t ∈ nhds (0 : E) := by
    simpa [t, ← mem_interior_iff_mem_nhds, interior_vadd,
      mem_vadd_set_iff_neg_vadd_mem] using ho
  have htbound : Bornology.IsBounded t := hb.vadd (-o)
  have htbounded := NormedSpace.isVonNBounded_of_isBounded ℝ htbound
  have htranslate : o +ᵥ t = s := by simp [t]
  let e := (translatedRadialGaugeHomeomorph htconv htzero htbounded o).trans
    (Homeomorph.setCongr (congrArg frontier htranslate))
  obtain ⟨R, hR, hnorm⟩ := htbound.exists_pos_norm_le
  have hball : t ⊆ Metric.closedBall 0 R := by
    intro x hx
    simpa using hnorm x hx
  obtain ⟨C, hC⟩ := exists_lipschitzWith_translatedRadialGaugeHomeomorph
    htconv htzero htbounded o hR hball
  refine ⟨fun u ↦ (gauge t u)⁻¹, e, C, ?_, ?_, ?_⟩
  · intro u hu
    have hune : u ≠ 0 := by intro h; simp [h] at hu
    have hg := (gauge_pos (absorbent_nhds_zero htzero) htbounded).mpr hune
    refine ⟨inv_pos.mpr hg, ?_, ?_⟩
    · have hm := (e ⟨u, hu⟩).property
      change (translatedRadialGaugeHomeomorph htconv htzero htbounded o ⟨u, hu⟩ : E)
        ∈ frontier s at hm
      rwa [translatedRadialGaugeHomeomorph_apply] at hm
    · intro r hr hru
      have hz : r • u ∈ frontier t := by
        change r • u ∈ frontier (-o +ᵥ s)
        rw [frontier, closure_vadd, interior_vadd]
        simpa only [frontier, Set.mem_sdiff, mem_vadd_set_iff_neg_vadd_mem, neg_neg, vadd_eq_add]
          using hru
      have hgauge := (gauge_eq_one_iff_mem_frontier htconv htzero).mpr hz
      rw [gauge_smul_of_nonneg hr.le, smul_eq_mul] at hgauge
      simpa only [one_div] using (eq_div_iff hg.ne').mpr hgauge
  · intro u
    exact translatedRadialGaugeHomeomorph_apply htconv htzero htbounded o u
  · exact hC
