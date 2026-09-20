import Mathlib.MeasureTheory.VectorMeasure.IntegrationByParts
import Mathlib.MeasureTheory.VectorMeasure.WithDensity

noncomputable section

open MeasureTheory Set
open scoped Topology

namespace MeasureTheory

/-- Integrating a bounded function against a real signed density multiplies the ordinary
integrand by that density. -/
theorem VectorMeasure.setIntegral_withDensity_mul_of_bounded
    {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] {r q : X → ℝ}
    (hr : Integrable r μ) (hq : AEStronglyMeasurable q μ) (C : ℝ)
    (hq_bound : ∀ x, ‖q x‖ ≤ C) (E : Set X) (hE : MeasurableSet E) :
    (∫ᵛ x in E, q x ∂[ContinuousLinearMap.mul ℝ ℝ; μ.withDensityᵥ r]) =
      ∫ x in E, q x * r x ∂μ := by
  rw [withDensityᵥ_eq_withDensity_pos_part_sub_withDensity_neg_part hr]
  let μp := μ.withDensity fun x ↦ ENNReal.ofReal (r x)
  let μn := μ.withDensity fun x ↦ ENNReal.ofReal (-r x)
  let _ : IsFiniteMeasure μp := isFiniteMeasure_withDensity_ofReal hr.2
  let _ : IsFiniteMeasure μn := isFiniteMeasure_withDensity_ofReal hr.neg.2
  have hqp : (μp.toSignedMeasure : SignedMeasure X).Integrable q := by
    rw [VectorMeasure.Integrable, Measure.variation_toSignedMeasure]
    exact Integrable.of_bound (hq.mono_ac (withDensity_absolutelyContinuous _ _)) C
      (ae_of_all _ hq_bound)
  have hqn : (μn.toSignedMeasure : SignedMeasure X).Integrable q := by
    rw [VectorMeasure.Integrable, Measure.variation_toSignedMeasure]
    exact Integrable.of_bound (hq.mono_ac (withDensity_absolutelyContinuous _ _)) C
      (ae_of_all _ hq_bound)
  have hmul : ContinuousLinearMap.mul ℝ ℝ =
      (ContinuousLinearMap.lsmul ℝ ℝ).flip := by
    ext; simp
  change ∫ᵛ x, q x ∂[ContinuousLinearMap.mul ℝ ℝ;
      ((μp.toSignedMeasure : SignedMeasure X) - μn.toSignedMeasure).restrict E] = _
  rw [VectorMeasure.restrict_sub,
    VectorMeasure.integral_sub_vectorMeasure hqp.restrict hqn.restrict]
  have hp : (∫ᵛ x in E, q x ∂[ContinuousLinearMap.mul ℝ ℝ; μp.toSignedMeasure]) =
      ∫ x in E, q x ∂μp := by
    rw [hmul]
    exact VectorMeasure.setIntegral_toSignedMeasure hE
  have hn : (∫ᵛ x in E, q x ∂[ContinuousLinearMap.mul ℝ ℝ; μn.toSignedMeasure]) =
      ∫ x in E, q x ∂μn := by
    rw [hmul]
    exact VectorMeasure.setIntegral_toSignedMeasure hE
  have hdp : ∫ x in E, q x ∂μp =
      ∫ x in E, (ENNReal.ofReal (r x)).toReal • q x ∂μ := by
    apply setIntegral_withDensity_eq_setIntegral_toReal_smul₀
    · exact hr.aestronglyMeasurable.aemeasurable.ennreal_ofReal.restrict
    · filter_upwards with x
      simp
    · exact hE
  have hdn : ∫ x in E, q x ∂μn =
      ∫ x in E, (ENNReal.ofReal (-r x)).toReal • q x ∂μ := by
    apply setIntegral_withDensity_eq_setIntegral_toReal_smul₀
    · exact hr.neg.aestronglyMeasurable.aemeasurable.ennreal_ofReal.restrict
    · filter_upwards with x
      simp
    · exact hE
  rw [hp, hn, hdp, hdn]
  have hip : Integrable (fun x ↦ (ENNReal.ofReal (r x)).toReal • q x) μ := by
    simpa only [ENNReal.toReal_ofReal', smul_eq_mul, mul_comm] using
      hr.pos_part.bdd_mul hq (ae_of_all _ hq_bound)
  have hin : Integrable (fun x ↦ (ENNReal.ofReal (-r x)).toReal • q x) μ := by
    simpa only [ENNReal.toReal_ofReal', smul_eq_mul, mul_comm] using
      hr.neg_part.bdd_mul hq (ae_of_all _ hq_bound)
  rw [← MeasureTheory.integral_sub hip.integrableOn hin.integrableOn]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  simp only [smul_eq_mul]
  rcases le_total 0 (r x) with hx | hx
  · rw [ENNReal.toReal_ofReal', ENNReal.toReal_ofReal']
    simp only [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx)]
    ring
  · rw [ENNReal.toReal_ofReal', ENNReal.toReal_ofReal']
    simp only [max_eq_right hx, max_eq_left (neg_nonneg.mpr hx)]
    ring

/-- Integrating a continuous real function on a compact space against a signed density
multiplies the ordinary integrand by that density. -/
theorem VectorMeasure.setIntegral_withDensity_mul
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X] [CompactSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] {r q : X → ℝ}
    (hr : Integrable r μ) (hq : Continuous q) (E : Set X) (hE : MeasurableSet E) :
    (∫ᵛ x in E, q x ∂[ContinuousLinearMap.mul ℝ ℝ; μ.withDensityᵥ r]) =
      ∫ x in E, q x * r x ∂μ := by
  let q' : BoundedContinuousFunction X ℝ :=
    ContinuousMap.equivBoundedOfCompact X ℝ ⟨q, hq⟩
  exact VectorMeasure.setIntegral_withDensity_mul_of_bounded hr hq.aestronglyMeasurable ‖q'‖
    (fun x ↦ BoundedContinuousFunction.norm_coe_le_norm q' x) E hE

end MeasureTheory
