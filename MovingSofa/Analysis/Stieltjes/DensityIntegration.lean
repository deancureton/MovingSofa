import MovingSofa.Analysis.Stieltjes.AbsoluteContinuity
import MovingSofa.ForMathlib.MeasureTheory.VectorMeasure.WithDensity

noncomputable section

open MeasureTheory Set
open scoped Topology

namespace MovingSofa

/-- A continuous integrand against an interval Stieltjes measure with an ordinary density is
the corresponding weighted Lebesgue integral on the interval subtype. -/
theorem intervalStieltjesIntegral_eq_integral_mul_of_density
    {a b : ℝ} (F : RightContinuousIntervalBV a b) {r : ℝ → ℝ}
    (hr : HasIntervalStieltjesDensity F r) {q : Icc a b → ℝ} (hq : Continuous q)
    (E : Set (Icc a b)) (hE : MeasurableSet E) :
    intervalStieltjesIntegral F q E =
      ∫ t in E, q t * r t ∂volume.comap (Subtype.val : Icc a b → ℝ) := by
  have hri : Integrable (fun t : Icc a b ↦ r t)
      (volume.comap (Subtype.val : Icc a b → ℝ)) :=
    (integrableOn_iff_comap_subtypeVal measurableSet_Icc).mp hr.1
  have hmeasure : intervalStieltjesMeasure F =
      (volume.comap (Subtype.val : Icc a b → ℝ)).withDensityᵥ
        (fun t : Icc a b ↦ r t) := by
    ext S hS
    have himage : MeasurableSet ((Subtype.val : Icc a b → ℝ) '' S) :=
      (MeasurableEmbedding.subtype_coe measurableSet_Icc).measurableSet_image' hS
    have hpre : {t : Icc a b | (t : ℝ) ∈ (Subtype.val : Icc a b → ℝ) '' S} = S :=
      Set.preimage_image_eq S Subtype.val_injective
    rw [withDensityᵥ_apply hri hS, ← hpre,
      integral_subtype_preimage measurableSet_Icc himage]
    exact hr.2 _ himage
  let _ : IsFiniteMeasure (volume.comap (Subtype.val : Icc a b → ℝ)) :=
    ⟨by
      rw [comap_subtype_coe_apply measurableSet_Icc]
      simp only [image_univ, Subtype.range_val]
      exact measure_Icc_lt_top⟩
  unfold intervalStieltjesIntegral
  rw [hmeasure]
  exact VectorMeasure.setIntegral_withDensity_mul hri hq E hE

/-- The density formula also applies to a bounded-variation integrand on a nonempty compact
interval. -/
theorem intervalStieltjesIntegral_eq_integral_mul_of_density_bv
    {a b : ℝ} (hab : a ≤ b) (F : RightContinuousIntervalBV a b) {r : ℝ → ℝ}
    (hr : HasIntervalStieltjesDensity F r) {q : Icc a b → ℝ}
    (hq : BoundedVariationOn q univ) (E : Set (Icc a b)) (hE : MeasurableSet E) :
    intervalStieltjesIntegral F q E =
      ∫ t in E, q t * r t ∂volume.comap (Subtype.val : Icc a b → ℝ) := by
  have hri : Integrable (fun t : Icc a b ↦ r t)
      (volume.comap (Subtype.val : Icc a b → ℝ)) :=
    (integrableOn_iff_comap_subtypeVal measurableSet_Icc).mp hr.1
  have hmeasure : intervalStieltjesMeasure F =
      (volume.comap (Subtype.val : Icc a b → ℝ)).withDensityᵥ
        (fun t : Icc a b ↦ r t) := by
    ext S hS
    have himage : MeasurableSet ((Subtype.val : Icc a b → ℝ) '' S) :=
      (MeasurableEmbedding.subtype_coe measurableSet_Icc).measurableSet_image' hS
    have hpre : {t : Icc a b | (t : ℝ) ∈ (Subtype.val : Icc a b → ℝ) '' S} = S :=
      Set.preimage_image_eq S Subtype.val_injective
    rw [withDensityᵥ_apply hri hS, ← hpre,
      integral_subtype_preimage measurableSet_Icc himage]
    exact hr.2 _ himage
  let _ : IsFiniteMeasure (volume.comap (Subtype.val : Icc a b → ℝ)) :=
    ⟨by
      rw [comap_subtype_coe_apply measurableSet_Icc]
      simp only [image_univ, Subtype.range_val]
      exact measure_Icc_lt_top⟩
  let t₀ : Icc a b := ⟨a, le_rfl, hab⟩
  let C := ‖q t₀‖ + (eVariationOn q univ).toReal
  have hq_bound : ∀ t, ‖q t‖ ≤ C := by
    intro t
    calc
      ‖q t‖ ≤ ‖q t₀‖ + ‖q t - q t₀‖ := norm_le_norm_add_norm_sub' _ _
      _ ≤ ‖q t₀‖ + (eVariationOn q univ).toReal := by
        gcongr
        simpa [dist_eq_norm_sub] using hq.dist_le (mem_univ t) (mem_univ t₀)
      _ = C := rfl
  unfold intervalStieltjesIntegral
  rw [hmeasure]
  exact VectorMeasure.setIntegral_withDensity_mul_of_bounded hri
    hq.stronglyMeasurable.aestronglyMeasurable C hq_bound E hE

/-- A real function agreeing with a BV representative is integrable on its interval. -/
theorem RightContinuousIntervalBV.integrableOn_Icc_of_eq
    {a b : ℝ} (f : RightContinuousIntervalBV a b) (q : ℝ → ℝ)
    (hq : ∀ t : Icc a b, q t = f.toFun t) : IntegrableOn q (Icc a b) := by
  have hfinite : IsFiniteMeasure (volume.comap (Subtype.val : Icc a b → ℝ)) :=
    ⟨by
      rw [comap_subtype_coe_apply measurableSet_Icc]
      simp only [image_univ, Subtype.range_val]
      exact measure_Icc_lt_top⟩
  let _ := hfinite
  rw [IntegrableOn, ← map_comap_subtype_coe measurableSet_Icc,
    (MeasurableEmbedding.subtype_coe measurableSet_Icc).integrable_map_iff
      (μ := volume.comap (Subtype.val : Icc a b → ℝ))]
  convert f.boundedVariation.integrable
      (μ := volume.comap (Subtype.val : Icc a b → ℝ)) using 1
  funext t
  exact hq t

end MovingSofa
