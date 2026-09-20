import Mathlib.Analysis.Complex.MeanValue
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

noncomputable section

open MeasureTheory

namespace Complex

private theorem integrableOn_polarCoord_target
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : ℝ × ℝ → F) (hg : Integrable g) :
    IntegrableOn (fun p : ℝ × ℝ ↦ p.1 • g (polarCoord.symm p))
      polarCoord.target := by
  have hinj : Set.InjOn (polarCoord.symm : ℝ × ℝ → ℝ × ℝ)
      polarCoord.target := by
    rw [← polarCoord.symm_source]
    exact polarCoord.symm.injOn
  have himage : polarCoord.symm '' polarCoord.target =
      polarCoord.source := by
    rw [← polarCoord.symm_source, ← polarCoord.symm_target]
    exact polarCoord.symm.image_source_eq_target
  have hj := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul
    (s := polarCoord.target) volume polarCoord.open_target.measurableSet
    (fun p _ ↦ (hasFDerivAt_polarCoord_symm p).hasFDerivWithinAt)
    hinj g).mp (by
      rw [himage]
      exact hg.integrableOn)
  refine hj.congr_fun ?_ polarCoord.open_target.measurableSet
  intro p hp
  dsimp only
  rw [det_fderivPolarCoordSymm, abs_of_pos hp.1]

private theorem integrableOn_complex_polarCoord_target
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℂ → F) (hf : Integrable f) :
    IntegrableOn (fun p : ℝ × ℝ ↦ p.1 • f (Complex.polarCoord.symm p))
      Complex.polarCoord.target := by
  rw [Complex.polarCoord_target]
  let g : ℝ × ℝ → F := f ∘ Complex.measurableEquivRealProd.symm
  have hg : Integrable g :=
    ((Complex.volume_preserving_equiv_real_prod.symm).integrable_comp_emb
      Complex.measurableEquivRealProd.symm.measurableEmbedding).mpr hf
  have h := integrableOn_polarCoord_target g hg
  change IntegrableOn
    (fun p ↦ p.1 • (f ∘ Complex.measurableEquivRealProd.symm)
      (polarCoord.symm p)) (Set.Ioi 0 ×ˢ Set.Ioo (-Real.pi) Real.pi) at h
  simpa only [Function.comp_apply,
    Complex.measurableEquivRealProd_symm_polarCoord_symm_apply] using h

private theorem integral_circleMap_Ioo_eq_circleAverage
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℂ → E) (r : ℝ) :
    (∫ θ in Set.Ioo (-Real.pi) Real.pi, f (circleMap 0 r θ)) =
      (2 * Real.pi) • Real.circleAverage f 0 r := by
  rw [Real.circleAverage_eq_integral_add (-Real.pi), smul_smul]
  have hp : (2 * Real.pi) * (2 * Real.pi)⁻¹ = 1 := by
    field_simp [Real.pi_ne_zero]
  rw [hp, one_smul, ← MeasureTheory.integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (le_of_lt (neg_lt_self Real.pi_pos))]
  have hshift := intervalIntegral.integral_comp_add_right
    (f := fun θ ↦ f (circleMap 0 r θ)) (a := 0) (b := 2 * Real.pi) (-Real.pi)
  simpa [two_mul] using hshift.symm

/-- The radial profile of the inverse distance truncated to a disk of radius `S`. -/
private def invNormCutoff (S r : ℝ) : ℝ := if r < S then r⁻¹ else 0

private theorem indicator_ball_inv_norm_eq (S : ℝ) :
    (fun p : ℂ ↦ (Metric.ball 0 S).indicator (fun p ↦ ‖p‖⁻¹) p) =
      fun p ↦ invNormCutoff S ‖p‖ := by
  funext p
  rw [Set.indicator]
  simp only [Metric.mem_ball, dist_zero_right, invNormCutoff]

private theorem radial_invNormCutoff_ae (S : ℝ) :
    (fun y : ℝ ↦ y ^ (Module.finrank ℝ ℂ - 1) • invNormCutoff S y)
      =ᵐ[volume.restrict (Set.Ioi 0)]
      (Set.Iio S).indicator (fun _ ↦ (1 : ℝ)) := by
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  have hy0 : y ≠ 0 := ne_of_gt hy
  simp [invNormCutoff, Set.indicator, smul_eq_mul, hy0]

/-- Inverse distance from zero is integrable on a complex disk centred at zero. -/
theorem integrableOn_inv_norm_ball (S : ℝ) :
    IntegrableOn (fun p : ℂ ↦ ‖p‖⁻¹) (Metric.ball 0 S) := by
  rw [← integrable_indicator_iff measurableSet_ball]
  show Integrable (fun p : ℂ ↦ (Metric.ball 0 S).indicator (fun p ↦ ‖p‖⁻¹) p)
  rw [indicator_ball_inv_norm_eq,
    MeasureTheory.integrable_fun_norm_addHaar volume (f := invNormCutoff S)]
  refine IntegrableOn.congr_fun_ae ?_ (radial_invNormCutoff_ae S).symm
  rw [integrableOn_indicator_iff measurableSet_Iio, Set.Iio_inter_Ioi]
  exact integrableOn_const (by simp)

/-- The integral of inverse distance from zero over a complex disk centred at zero. -/
theorem setIntegral_inv_norm_ball (S : ℝ) (hS : 0 < S) :
    (∫ p : ℂ in Metric.ball 0 S, ‖p‖⁻¹) = 2 * Real.pi * S := by
  rw [← integral_indicator (f := fun p : ℂ ↦ ‖p‖⁻¹) measurableSet_ball,
    indicator_ball_inv_norm_eq,
    MeasureTheory.integral_fun_norm_addHaar volume (invNormCutoff S),
    integral_congr_ae (radial_invNormCutoff_ae S),
    setIntegral_indicator measurableSet_Iio, Set.Ioi_inter_Iio]
  simp [hS.le, Measure.real, Complex.volume_ball, mul_assoc]

private theorem integrableOn_inv_sub_ball (R : ℝ) (a : ℂ) (ha : ‖a‖ < R) :
    IntegrableOn (fun q : ℂ ↦ (a - q)⁻¹) (Metric.ball 0 R) := by
  rw [← integrable_indicator_iff measurableSet_ball]
  let g : ℂ → ℝ :=
    (Metric.ball a (2 * R)).indicator (fun q ↦ ‖a - q‖⁻¹)
  have hg : Integrable g := by
    have hcenter : (fun q : ℂ ↦
        (Metric.ball a (2 * R)).indicator (fun q ↦ ‖a - q‖⁻¹) q) =
        fun q ↦ (Metric.ball 0 (2 * R)).indicator (fun w ↦ ‖w‖⁻¹) (a - q) := by
      funext q
      have hm : q ∈ Metric.ball a (2 * R) ↔ a - q ∈ Metric.ball 0 (2 * R) := by
        simp only [Metric.mem_ball, dist_eq_norm]
        simp [sub_zero, norm_sub_rev]
      by_cases hq : q ∈ Metric.ball a (2 * R)
      · simp [hq, hm.mp hq]
      · simp [hq, mt hm.mpr hq]
    change Integrable (fun q : ℂ ↦
      (Metric.ball a (2 * R)).indicator (fun q ↦ ‖a - q‖⁻¹) q)
    rw [hcenter, MeasureTheory.integrable_comp_sub_left]
    exact (integrable_indicator_iff measurableSet_ball).mpr
      (integrableOn_inv_norm_ball (2 * R))
  refine Integrable.mono' hg ?_ ?_
  · exact ((measurable_const.sub measurable_id).inv.indicator
      measurableSet_ball).aestronglyMeasurable
  · filter_upwards with q
    by_cases hq : q ∈ Metric.ball (0 : ℂ) R
    · have hqa : q ∈ Metric.ball a (2 * R) := by
        rw [Metric.mem_ball, dist_eq_norm]
        have hqR : ‖q‖ < R := by simpa [Metric.mem_ball, dist_eq_norm] using hq
        calc
          ‖q - a‖ ≤ ‖q‖ + ‖a‖ := norm_sub_le q a
          _ < R + R := add_lt_add hqR ha
          _ = 2 * R := by ring
      simp only [Set.indicator_of_mem hq, norm_inv]
      simp [g, hqa]
    · simp only [Set.indicator, hq, ↓reduceIte, norm_zero]
      exact Set.indicator_apply_nonneg fun _ ↦ by positivity

private theorem circleAverage_inv_sub_eq_inv_of_radius_lt_norm
    (a : ℂ) (r : ℝ) (hr : 0 ≤ r) (hout : r < ‖a‖) :
    Real.circleAverage (fun w ↦ (a - w)⁻¹) 0 r = a⁻¹ := by
  have hne : ∀ w ∈ Metric.closedBall (0 : ℂ) |r|, a - w ≠ 0 := by
    intro w hw hwa
    have hwa' : w = a := (sub_eq_zero.mp hwa).symm
    subst a
    have : ‖w‖ ≤ r := by simpa [abs_of_nonneg hr, dist_eq_norm] using hw
    linarith
  have hcont : ContinuousOn (fun w : ℂ ↦ (a - w)⁻¹) (Metric.closedBall 0 |r|) :=
    ((continuous_const.sub continuous_id).continuousOn).inv₀ hne
  have hdiff : DiffContOnCl ℂ (fun w : ℂ ↦ (a - w)⁻¹) (Metric.ball 0 |r|) :=
    DiffContOnCl.mk_ball
      (fun w hw ↦ (((differentiableAt_const a).sub differentiableAt_id).inv
        (hne w (Metric.ball_subset_closedBall hw))).differentiableWithinAt) hcont
  simpa using hdiff.circleAverage

private theorem partialFraction_circleIntegral_congr (a : ℂ) (r : ℝ) (hr : 0 < r)
    (ha : a ≠ 0) (hra : ‖a‖ ≠ r) :
    (∮ w in C(0, r), (w - 0)⁻¹ * (a - w)⁻¹) =
      ∮ w in C(0, r), a⁻¹ * ((w - 0)⁻¹ - (w - a)⁻¹) := by
  refine circleIntegral.integral_congr hr.le fun w hw ↦ ?_
  have hw0 : w ≠ 0 := by
    intro h
    subst w
    have hz : (0 : ℝ) = r := by simpa using (Metric.mem_sphere.mp hw)
    linarith
  have hwa : w ≠ a := by
    intro h
    subst w
    exact hra (by simpa [dist_eq_norm] using (Metric.mem_sphere.mp hw))
  field_simp
  ring

private theorem circleIntegrable_sub_inv_of_norm_ne (a : ℂ) (r : ℝ) (hr : 0 < r)
    (hra : ‖a‖ ≠ r) : CircleIntegrable (fun w : ℂ ↦ (w - a)⁻¹) 0 r :=
  circleIntegrable_sub_inv_iff.mpr (Or.inr fun h ↦
    hra (by simpa [dist_eq_norm, abs_of_pos hr] using (Metric.mem_sphere.mp h)))

private theorem circleAverage_inv_sub_eq_zero_of_norm_lt_radius
    (a : ℂ) (r : ℝ) (hr : 0 < r) (ha : a ≠ 0) (hinner : ‖a‖ < r) :
    Real.circleAverage (fun w ↦ (a - w)⁻¹) 0 r = 0 := by
  rw [Real.circleAverage_eq_circleIntegral hr.ne']
  change (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
      (∮ z in C(0, r), (z - 0)⁻¹ * (a - z)⁻¹) = 0
  have hmem : a ∈ Metric.ball (0 : ℂ) r := by
    simpa [Metric.mem_ball, dist_eq_norm] using hinner
  rw [partialFraction_circleIntegral_congr a r hr ha hinner.ne,
    circleIntegral.integral_const_mul,
    circleIntegral.integral_sub
      (circleIntegrable_sub_inv_of_norm_ne 0 r hr (by simpa using hr.ne))
      (circleIntegrable_sub_inv_of_norm_ne a r hr hinner.ne),
    circleIntegral.integral_sub_center_inv 0 hr.ne',
    circleIntegral.integral_sub_inv_of_mem_ball hmem]
  simp

private theorem setIntegral_inv_sub_ball_of_ne_zero (R : ℝ) (a : ℂ) (ha0 : a ≠ 0)
    (ha : ‖a‖ < R) :
    (∫ q in Metric.ball 0 R, (a - q)⁻¹) = Real.pi * starRingEnd ℂ a := by
  let f : ℂ → ℂ := (Metric.ball 0 R).indicator (fun q ↦ (a - q)⁻¹)
  have hf : Integrable f :=
    (integrable_indicator_iff measurableSet_ball).mpr (integrableOn_inv_sub_ball R a ha)
  have hpInt := integrableOn_complex_polarCoord_target f hf
  have hpolar := Complex.integral_comp_polarCoord_symm f
  have hprod :
      (∫ p in polarCoord.target,
        p.1 • f (Complex.polarCoord.symm p)) =
        ∫ r in Set.Ioi (0 : ℝ), ∫ θ in Set.Ioo (-Real.pi) Real.pi,
          r • f (Complex.polarCoord.symm (r, θ)) := by
    change (∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi,
      p.1 • f (Complex.polarCoord.symm p)) = _
    exact setIntegral_prod _ (by
      rw [← Measure.volume_eq_prod ℝ ℝ]
      simpa only [Complex.polarCoord_target] using hpInt)
  rw [← integral_indicator measurableSet_ball]
  change (∫ q, f q) = _
  rw [← hpolar, hprod]
  have hinner : ∀ r ∈ Set.Ioi (0 : ℝ),
      (∫ θ in Set.Ioo (-Real.pi) Real.pi,
          r • f (Complex.polarCoord.symm (r, θ))) =
        if r < R then r • ((2 * Real.pi) •
          Real.circleAverage (fun q ↦ (a - q)⁻¹) 0 r) else 0 := by
    intro r hr
    have hr0 : 0 < r := hr
    have hpoint : ∀ θ, Complex.polarCoord.symm (r, θ) = circleMap 0 r θ := by
      intro θ
      rw [Complex.polarCoord_symm_apply, circleMap_zero, Complex.exp_mul_I]
      simp
    by_cases hrR : r < R
    · simp only [hrR, ↓reduceIte]
      have hmem : ∀ θ, Complex.polarCoord.symm (r, θ) ∈ Metric.ball (0 : ℂ) R := by
        intro θ
        rw [hpoint]
        simpa [Metric.mem_ball, dist_eq_norm, abs_of_pos hr0] using hrR
      simp_rw [f, Set.indicator_of_mem (hmem _), hpoint]
      rw [integral_smul]
      rw [integral_circleMap_Ioo_eq_circleAverage (fun q ↦ (a - q)⁻¹) r]
    · simp only [hrR, ↓reduceIte]
      have hnotmem : ∀ θ, Complex.polarCoord.symm (r, θ) ∉ Metric.ball (0 : ℂ) R := by
        intro θ hθ
        rw [hpoint] at hθ
        have : r < R := by
          simpa [Metric.mem_ball, dist_eq_norm, abs_of_pos hr0] using hθ
        exact hrR this
      simp_rw [f, Set.indicator, hnotmem]
      simp
  rw [setIntegral_congr_fun measurableSet_Ioi hinner]
  have hradial :
      (fun r : ℝ ↦ if r < R then r • ((2 * Real.pi) •
        Real.circleAverage (fun q ↦ (a - q)⁻¹) 0 r) else 0)
        =ᵐ[volume.restrict (Set.Ioi 0)]
      fun r ↦ if r < ‖a‖ then r • ((2 * Real.pi) • a⁻¹) else 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi,
      ae_restrict_of_ae (Measure.ae_ne volume ‖a‖)] with r hr hra
    have hr0 : 0 < r := hr
    by_cases hra' : r < ‖a‖
    · have hrR : r < R := hra'.trans ha
      simp only [hrR, hra', ↓reduceIte]
      rw [circleAverage_inv_sub_eq_inv_of_radius_lt_norm a r hr0.le hra']
    · have har : ‖a‖ < r := lt_of_le_of_ne (le_of_not_gt hra') (Ne.symm hra)
      by_cases hrR : r < R
      · simp only [hrR, hra', ↓reduceIte]
        rw [circleAverage_inv_sub_eq_zero_of_norm_lt_radius a r hr0 ha0 har, smul_zero]
        simp
      · simp only [hrR, hra', ↓reduceIte]
  rw [integral_congr_ae hradial]
  rw [show (fun r : ℝ ↦ if r < ‖a‖ then r • ((2 * Real.pi) • a⁻¹) else 0) =
      (Set.Iio ‖a‖).indicator (fun r ↦ r • ((2 * Real.pi) • a⁻¹)) by
    funext r
    simp [Set.indicator]]
  rw [setIntegral_indicator measurableSet_Iio, Set.Ioi_inter_Iio]
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (norm_nonneg a)]
  rw [intervalIntegral.integral_smul_const]
  rw [integral_id]
  rw [Complex.inv_def]
  simp only [starRingEnd_apply, Complex.normSq_eq_norm_sq, Complex.real_smul]
  have hnorm : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr ha0
  have hnormc : (‖a‖ : ℂ) ≠ 0 := by exact_mod_cast hnorm
  push_cast
  field_simp [hnormc]
  ring

private theorem setIntegral_inv_sub_ball_zero (R : ℝ) :
    (∫ q in Metric.ball 0 R, ((0 : ℂ) - q)⁻¹) = 0 := by
  rw [← integral_indicator (f := fun q : ℂ ↦ ((0 : ℂ) - q)⁻¹) measurableSet_ball]
  let f : ℂ → ℂ := (Metric.ball 0 R).indicator (fun q ↦ ((0 : ℂ) - q)⁻¹)
  have hodd : ∀ q, f (-q) = -f q := by
    intro q
    have hm : -q ∈ Metric.ball (0 : ℂ) R ↔ q ∈ Metric.ball 0 R := by
      simp [Metric.mem_ball, dist_eq_norm]
    by_cases hq : q ∈ Metric.ball (0 : ℂ) R
    · simp [f, hq, hm.mpr hq]
    · simp [f, hq, mt hm.mp hq]
  have hneg : (∫ q, f (-q)) = -(∫ q, f q) := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hodd), integral_neg]
  have hself : (∫ q, f q) = -(∫ q, f q) :=
    (MeasureTheory.integral_neg_eq_self f volume).symm.trans hneg
  have ht : (2 : ℝ) • (∫ q, f q) = 0 := by
    rw [two_smul]
    calc
      (∫ q, f q) + ∫ q, f q = -(∫ q, f q) + ∫ q, f q :=
        congrArg (fun x ↦ x + ∫ q, f q) hself
      _ = 0 := neg_add_cancel _
  exact (smul_eq_zero.mp ht).resolve_left (by norm_num)

/-- The integral of `q ↦ (a - q)⁻¹` over a disk centred at zero containing `a`. -/
theorem setIntegral_inv_sub_ball (R : ℝ) (a : ℂ) (ha : ‖a‖ < R) :
    (∫ q in Metric.ball 0 R, (a - q)⁻¹) = Real.pi * starRingEnd ℂ a := by
  by_cases ha0 : a = 0
  · subst a
    simpa using setIntegral_inv_sub_ball_zero R
  · exact setIntegral_inv_sub_ball_of_ne_zero R a ha0 ha

end Complex
