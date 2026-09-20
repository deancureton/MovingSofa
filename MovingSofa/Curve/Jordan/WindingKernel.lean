import MovingSofa.Geometry.Plane
import MovingSofa.ForMathlib.Analysis.Complex.DiskIntegral

noncomputable section

open MeasureTheory

namespace MovingSofa

/-- The inverse-distance vector kernel based at `z`. -/
def windingKernel (z p : Point) : Point :=
  (‖z - p‖ ^ 2)⁻¹ • (z - p)

private def pointComplex : Point ≃ₗᵢ[ℝ] ℂ :=
  Complex.orthonormalBasisOneI.repr.symm

private theorem pointComplex_windingKernel (z p : Point) :
    pointComplex (windingKernel z p) =
      (starRingEnd ℂ (pointComplex z - pointComplex p))⁻¹ := by
  have hsub : pointComplex (z - p) = pointComplex z - pointComplex p :=
    map_sub pointComplex z p
  rw [windingKernel, map_smul, hsub]
  let v : ℂ := pointComplex z - pointComplex p
  change (‖z - p‖ ^ 2)⁻¹ • v = (starRingEnd ℂ v)⁻¹
  rw [Complex.inv_def]
  simp only [starRingEnd_apply, star_star, Complex.normSq_eq_norm_sq, norm_star]
  have hn : ‖v‖ = ‖z - p‖ := by
    rw [show v = pointComplex (z - p) by simp [v, hsub]]
    exact LinearIsometryEquiv.norm_map pointComplex (z - p)
  rw [hn, Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_pow]
  ring

private theorem norm_windingKernel (z p : Point) :
    ‖windingKernel z p‖ = if p = z then 0 else ‖z - p‖⁻¹ := by
  by_cases hp : p = z
  · subst p
    simp [windingKernel]
  · have hnorm : ‖z - p‖ ≠ 0 := by
      simpa [norm_eq_zero, sub_eq_zero] using Ne.symm hp
    rw [windingKernel, norm_smul, Real.norm_eq_abs]
    simp only [abs_inv, abs_pow, abs_norm]
    simp only [hp, ↓reduceIte]
    field_simp

private theorem ball_zero_subset_ball_two_mul (R : ℝ) (z : Point)
    (hz : ‖z‖ < R) : Metric.ball 0 R ⊆ Metric.ball z (2 * R) := by
  intro p hp
  rw [Metric.mem_ball, dist_eq_norm] at hp ⊢
  have hp' : ‖p‖ < R := by simpa using hp
  calc
    ‖p - z‖ ≤ ‖p‖ + ‖z‖ := norm_sub_le p z
    _ < R + R := add_lt_add hp' hz
    _ = 2 * R := by ring

private theorem measurable_windingKernel (z : Point) : Measurable (windingKernel z) := by
  unfold windingKernel
  exact (((measurable_const.sub measurable_id).norm.pow_const 2).inv.smul
    (measurable_const.sub measurable_id))

private theorem indicator_inv_norm_pointComplex (S : ℝ) (p : Point) :
    (Metric.ball (0 : Point) S).indicator (fun p ↦ ‖p‖⁻¹) p =
      (Metric.ball (0 : ℂ) S).indicator (fun q ↦ ‖q‖⁻¹) (pointComplex p) := by
  have hm : pointComplex p ∈ Metric.ball (0 : ℂ) S ↔
      p ∈ Metric.ball (0 : Point) S := by
    simp [Metric.mem_ball, dist_eq_norm]
  by_cases hp : p ∈ Metric.ball (0 : Point) S
  · simp [hp, hm.mpr hp]
  · simp [hp, mt hm.mp hp]

private theorem integrableOn_inv_norm_ball (S : ℝ) :
    IntegrableOn (fun p : Point ↦ ‖p‖⁻¹) (Metric.ball 0 S) := by
  rw [← integrable_indicator_iff measurableSet_ball]
  have hf : Integrable ((Metric.ball (0 : ℂ) S).indicator fun q ↦ ‖q‖⁻¹) :=
    (integrable_indicator_iff measurableSet_ball).mpr (Complex.integrableOn_inv_norm_ball S)
  refine (((LinearIsometryEquiv.measurePreserving pointComplex).integrable_comp_emb
    pointComplex.toHomeomorph.measurableEmbedding).mpr hf).congr ?_
  filter_upwards with p
  exact (indicator_inv_norm_pointComplex S p).symm

private theorem setIntegral_inv_norm_ball (S : ℝ) (hS : 0 < S) :
    (∫ p : Point in Metric.ball 0 S, ‖p‖⁻¹) = 2 * Real.pi * S := by
  rw [← integral_indicator (f := fun p : Point ↦ ‖p‖⁻¹) measurableSet_ball]
  calc
    (∫ p : Point, (Metric.ball 0 S).indicator (fun p ↦ ‖p‖⁻¹) p) =
        ∫ p : Point, (Metric.ball (0 : ℂ) S).indicator (fun q ↦ ‖q‖⁻¹) (pointComplex p) :=
      integral_congr_ae (Filter.Eventually.of_forall (indicator_inv_norm_pointComplex S))
    _ = ∫ q : ℂ, (Metric.ball (0 : ℂ) S).indicator (fun q ↦ ‖q‖⁻¹) q :=
      (LinearIsometryEquiv.measurePreserving pointComplex).integral_comp
        pointComplex.toHomeomorph.measurableEmbedding _
    _ = 2 * Real.pi * S := by
      rw [integral_indicator measurableSet_ball]
      exact Complex.setIntegral_inv_norm_ball S hS

private theorem indicator_centered_inv_norm_eq (z : Point) (S : ℝ) :
    (Metric.ball z S).indicator (fun p ↦ ‖z - p‖⁻¹) =
      fun p ↦ (Metric.ball 0 S).indicator (fun q ↦ ‖q‖⁻¹) (z - p) := by
  funext p
  have hm : p ∈ Metric.ball z S ↔ z - p ∈ Metric.ball 0 S := by
    simp only [Metric.mem_ball, dist_eq_norm]
    simp [sub_zero, norm_sub_rev]
  by_cases hp : p ∈ Metric.ball z S
  · simp [hp, hm.mp hp]
  · simp [hp, mt hm.mpr hp]

private theorem indicator_centered_inv_norm_nonneg (z : Point) (S : ℝ) (p : Point) :
    0 ≤ (Metric.ball z S).indicator (fun p ↦ ‖z - p‖⁻¹) p :=
  Set.indicator_apply_nonneg fun _ ↦ by positivity

private theorem integrable_indicator_centered_inv_norm (z : Point) (S : ℝ) :
    Integrable ((Metric.ball z S).indicator fun p ↦ ‖z - p‖⁻¹) := by
  rw [indicator_centered_inv_norm_eq, MeasureTheory.integrable_comp_sub_left]
  exact (integrable_indicator_iff measurableSet_ball).mpr (integrableOn_inv_norm_ball S)

private theorem integral_indicator_centered_inv_norm (z : Point) (S : ℝ) (hS : 0 < S) :
    (∫ p : Point, (Metric.ball z S).indicator (fun p ↦ ‖z - p‖⁻¹) p) = 2 * Real.pi * S := by
  rw [indicator_centered_inv_norm_eq,
    MeasureTheory.integral_sub_left_eq_self _ volume z, integral_indicator measurableSet_ball]
  exact setIntegral_inv_norm_ball S hS

private theorem norm_windingKernel_le_indicator (R : ℝ) (z : Point) (hz : ‖z‖ < R) :
    (fun p ↦ ‖windingKernel z p‖) ≤ᵐ[volume.restrict (Metric.ball 0 R)]
      (Metric.ball z (2 * R)).indicator (fun p ↦ ‖z - p‖⁻¹) := by
  filter_upwards [ae_restrict_mem measurableSet_ball] with p hp
  have hpz : p ∈ Metric.ball z (2 * R) := ball_zero_subset_ball_two_mul R z hz hp
  rw [norm_windingKernel]
  by_cases heq : p = z
  · simp only [heq, ↓reduceIte]
    exact indicator_centered_inv_norm_nonneg z (2 * R) z
  · simp [heq, hpz]

/-- The winding kernel is integrable on a disk containing its base point. -/
theorem integrableOn_windingKernel_ball (R : ℝ) (z : Point) (hz : ‖z‖ < R) :
    IntegrableOn (windingKernel z) (Metric.ball 0 R) :=
  Integrable.mono' (integrable_indicator_centered_inv_norm z (2 * R)).integrableOn
    (measurable_windingKernel z).aestronglyMeasurable
    (norm_windingKernel_le_indicator R z hz)

/-- The norm of the winding kernel has an integrable uniform majorant on an interior disk. -/
theorem setIntegral_norm_windingKernel_ball_le
    (R : ℝ) (hR : 0 < R) (z : Point) (hz : ‖z‖ < R) :
    (∫ p in Metric.ball 0 R, ‖windingKernel z p‖) ≤ 4 * Real.pi * R := by
  have hg : Integrable ((Metric.ball z (2 * R)).indicator fun p ↦ ‖z - p‖⁻¹) :=
    integrable_indicator_centered_inv_norm z (2 * R)
  calc
    (∫ p in Metric.ball 0 R, ‖windingKernel z p‖) ≤
        ∫ p in Metric.ball 0 R, (Metric.ball z (2 * R)).indicator (fun p ↦ ‖z - p‖⁻¹) p :=
      setIntegral_mono_ae_restrict (integrableOn_windingKernel_ball R z hz).norm
        hg.integrableOn (norm_windingKernel_le_indicator R z hz)
    _ ≤ ∫ p, (Metric.ball z (2 * R)).indicator (fun p ↦ ‖z - p‖⁻¹) p :=
      setIntegral_le_integral hg
        (Filter.Eventually.of_forall (indicator_centered_inv_norm_nonneg z (2 * R)))
    _ = 2 * Real.pi * (2 * R) :=
      integral_indicator_centered_inv_norm z (2 * R) (by linarith)
    _ = 4 * Real.pi * R := by ring

/-- The integral of the winding kernel over a disk is `π` times its base point. -/
theorem setIntegral_windingKernel_ball (R : ℝ) (z : Point) (hz : ‖z‖ < R) :
    (∫ p in Metric.ball 0 R, windingKernel z p) = Real.pi • z := by
  have hInt := integrableOn_windingKernel_ball R z hz
  let T : Point ≃ₗᵢ[ℝ] ℂ := pointComplex.trans Complex.conjLIE
  let a : ℂ := T z
  have ha : ‖a‖ < R := by simpa [a, T] using hz
  have hc := Complex.setIntegral_inv_sub_ball R a ha
  let G : ℂ → ℂ := (Metric.ball 0 R).indicator (fun q ↦ (a - q)⁻¹)
  have hpres := (LinearIsometryEquiv.measurePreserving T).integral_comp
    T.toHomeomorph.measurableEmbedding G
  have hfun : ∀ p : Point,
      G (T p) = (Metric.ball 0 R).indicator
        (fun p ↦ pointComplex (windingKernel z p)) p := by
    intro p
    have hm : T p ∈ Metric.ball (0 : ℂ) R ↔ p ∈ Metric.ball (0 : Point) R := by
      simp [Metric.mem_ball, dist_eq_norm, T]
    by_cases hp : p ∈ Metric.ball (0 : Point) R
    · rw [show G (T p) = (a - T p)⁻¹ by simp [G, hm.mpr hp]]
      rw [show (Metric.ball (0 : Point) R).indicator
          (fun p ↦ pointComplex (windingKernel z p)) p =
          pointComplex (windingKernel z p) by simp [hp]]
      rw [pointComplex_windingKernel]
      simp only [a, T, LinearIsometryEquiv.trans_apply, Complex.conjLIE_apply,
        map_sub]
    · rw [show G (T p) = 0 by simp [G, mt hm.mp hp]]
      simp [hp]
  have htransport :
      (∫ q in Metric.ball 0 R, (a - q)⁻¹) =
        pointComplex (∫ p in Metric.ball 0 R, windingKernel z p) := by
    rw [← integral_indicator measurableSet_ball]
    change (∫ q, G q) = _
    rw [← hpres]
    rw [integral_congr_ae (Filter.Eventually.of_forall hfun)]
    rw [integral_indicator measurableSet_ball]
    simpa using
      (pointComplex.toContinuousLinearEquiv.toContinuousLinearMap.integral_comp_comm hInt)
  apply pointComplex.injective
  rw [← htransport, hc]
  simp [a, T, Complex.real_smul]

/-- Off the range of a continuous interval path, each coordinate of the winding kernel is
a bounded continuous function of the parameter. -/
theorem windingKernel_coord_continuous_bounded
    {a b : ℝ} {x : Set.Icc a b → Point} (hx : Continuous x) {p : Point}
    (hp : p ∉ Set.range x) (i : Fin 2) :
    Continuous (fun t ↦ windingKernel (x t) p i) ∧
      ∃ C : ℝ, ∀ t, |windingKernel (x t) p i| ≤ C := by
  have hsub : Continuous (fun t ↦ x t - p) := hx.sub continuous_const
  have hne : ∀ t, ‖x t - p‖ ^ 2 ≠ 0 := by
    intro t
    apply pow_ne_zero
    rw [norm_ne_zero_iff]
    intro h
    exact hp ⟨t, sub_eq_zero.mp h⟩
  have hkernel : Continuous (fun t ↦ windingKernel (x t) p) := by
    unfold windingKernel
    exact ((hsub.norm.pow 2).inv₀ hne).smul hsub
  have hcoord : Continuous (fun t ↦ windingKernel (x t) p i) :=
    (PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) i).comp hkernel
  refine ⟨hcoord, ?_⟩
  have hbdd : BddAbove ((fun t ↦ |windingKernel (x t) p i|) '' Set.univ) :=
    isCompact_univ.bddAbove_image hcoord.abs.continuousOn
  obtain ⟨C, hC⟩ := hbdd
  exact ⟨C, fun t ↦ hC ⟨t, Set.mem_univ t, rfl⟩⟩

end MovingSofa
