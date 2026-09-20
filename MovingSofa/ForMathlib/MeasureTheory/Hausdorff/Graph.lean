import MovingSofa.ForMathlib.MeasureTheory.Hausdorff.Arclength

noncomputable section

open Filter
open scoped Topology

namespace MeasureTheory

private theorem map_firstCoordinate_restrict_curve_Icc
    (γ : ℝ → (EuclideanSpace ℝ (Fin 2))) (a b c d : ℝ)
    (hcoord : ∀ x ∈ Set.Icc a b, γ x 0 = x) :
    Measure.map (fun p : (EuclideanSpace ℝ (Fin 2)) ↦ p 0)
      ((Measure.hausdorffMeasure 1).restrict (γ '' Set.Icc a b)) (Set.Icc c d) =
      Measure.hausdorffMeasure 1 (γ '' Set.Icc (max a c) (min b d)) := by
  have hm : Measurable (fun p : (EuclideanSpace ℝ (Fin 2)) ↦ p 0) :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 ↦ ℝ) 0).continuous.measurable
  rw [Measure.map_apply hm measurableSet_Icc,
    Measure.restrict_apply (hm measurableSet_Icc)]
  congr 1
  ext p
  constructor
  · rintro ⟨hp, x, hx, rfl⟩
    refine ⟨x, ?_, rfl⟩
    change γ x 0 ∈ Set.Icc c d at hp
    rw [hcoord x hx] at hp
    exact ⟨max_le hx.1 hp.1, le_min hx.2 hp.2⟩
  · rintro ⟨x, hx, rfl⟩
    refine ⟨?_, x, ⟨(le_max_left _ _).trans hx.1, hx.2.trans (min_le_left _ _)⟩, rfl⟩
    change γ x 0 ∈ Set.Icc c d
    rw [hcoord x ⟨(le_max_left _ _).trans hx.1, hx.2.trans (min_le_left _ _)⟩]
    exact ⟨(le_max_right _ _).trans hx.1, hx.2.trans (min_le_right _ _)⟩

/-- Projected Hausdorff measure on a Lipschitz graph has speed as its density. -/
theorem map_firstCoordinate_restrict_curve_eq_withDensity
    {γ : ℝ → (EuclideanSpace ℝ (Fin 2))} {C : NNReal} {a b : ℝ} (hab : a ≤ b)
    (hγ : LipschitzOnWith C γ (Set.Icc a b)) (hcoord : ∀ x ∈ Set.Icc a b, γ x 0 = x) :
    Measure.map (fun p : (EuclideanSpace ℝ (Fin 2)) ↦ p 0)
      ((Measure.hausdorffMeasure 1).restrict (γ '' Set.Icc a b)) =
      (volume.restrict (Set.Icc a b)).withDensity (fun x ↦ ENNReal.ofReal ‖deriv γ x‖) := by
  have hinj : Set.InjOn γ (Set.Icc a b) := by
    intro x hx y hy hxy
    simpa only [hcoord x hx, hcoord y hy] using congrArg (fun p : (EuclideanSpace ℝ (Fin 2)) ↦ p 0) hxy
  have hfinite : Measure.hausdorffMeasure 1 (γ '' Set.Icc a b) ≠ ⊤ := by
    rw [hausdorffMeasure_image_Icc_eq_ofReal_integral_norm_deriv hab hγ hinj]
    exact ENNReal.ofReal_ne_top
  let _ : IsFiniteMeasure ((Measure.hausdorffMeasure 1).restrict (γ '' Set.Icc a b)) :=
    (isFiniteMeasure_restrict).mpr hfinite
  apply Measure.ext_of_Icc
  intro c d _
  rw [map_firstCoordinate_restrict_curve_Icc γ a b c d hcoord,
    withDensity_apply _ measurableSet_Icc,
    Measure.restrict_restrict measurableSet_Icc]
  have hinter : Set.Icc c d ∩ Set.Icc a b = Set.Icc (max a c) (min b d) := by
    rw [Set.Icc_inter_Icc]
    simp only [max_comm, min_comm]
  rw [hinter]
  by_cases hcd : max a c ≤ min b d
  · have hsub : Set.Icc (max a c) (min b d) ⊆ Set.Icc a b :=
      Set.Icc_subset_Icc (le_max_left _ _) (min_le_left _ _)
    rw [hausdorffMeasure_image_Icc_eq_ofReal_integral_norm_deriv hcd
      (hγ.mono hsub) (hinj.mono hsub)]
    rw [intervalIntegral.integral_of_le hcd, ← integral_Icc_eq_integral_Ioc]
    exact ofReal_integral_eq_lintegral_ofReal
      (IntegrableOn.mono_set (integrableOn_deriv_of_lipschitzOn hγ).norm hsub)
      (Filter.Eventually.of_forall fun _ ↦ norm_nonneg _)
  · rw [Set.Icc_eq_empty_of_lt (lt_of_not_ge hcd)]
    simp

/-- Weighted arclength formula for a planar Lipschitz graph on a compact interval. -/
theorem integral_restrict_curve_eq_integral_norm_deriv_mul
    {γ : ℝ → (EuclideanSpace ℝ (Fin 2))} {C : NNReal} {a b : ℝ} (hab : a ≤ b)
    (hγ : LipschitzOnWith C γ (Set.Icc a b)) (hcoord : ∀ x ∈ Set.Icc a b, γ x 0 = x)
    {φ : (EuclideanSpace ℝ (Fin 2)) → ℝ} (hφ : Measurable φ) :
    (∫ p, φ p ∂(Measure.hausdorffMeasure 1).restrict (γ '' Set.Icc a b)) =
      ∫ x in a..b, ‖deriv γ x‖ * φ (γ x) := by
  let γc : ℝ → (EuclideanSpace ℝ (Fin 2)) := fun x ↦ γ (max a (min x b))
  have hc : Continuous γc := hγ.continuousOn.comp_continuous
    (continuous_const.max (continuous_id.min continuous_const))
    (fun x ↦ ⟨le_max_left _ _, max_le hab (min_le_right _ _)⟩)
  have hceq (x : ℝ) (hx : x ∈ Set.Icc a b) : γc x = γ x := by
    simp only [γc, min_eq_left hx.2, max_eq_right hx.1]
  have hm : Measurable (fun p : (EuclideanSpace ℝ (Fin 2)) ↦ p 0) :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 ↦ ℝ) 0).continuous.measurable
  have hset : MeasurableSet (γ '' Set.Icc a b) :=
    (isCompact_Icc.image_of_continuousOn hγ.continuousOn).measurableSet
  have heq : (fun p ↦ φ (γc (p 0))) =ᵐ[
      (Measure.hausdorffMeasure 1).restrict (γ '' Set.Icc a b)] φ := by
    filter_upwards [ae_restrict_mem hset] with p hp
    obtain ⟨x, hx, rfl⟩ := hp
    rw [hcoord x hx, hceq x hx]
  rw [← integral_congr_ae heq,
    ← integral_map (μ := (Measure.hausdorffMeasure 1).restrict (γ '' Set.Icc a b))
      (f := fun x : ℝ ↦ φ (γc x)) hm.aemeasurable
      (hφ.comp hc.measurable).aestronglyMeasurable,
    map_firstCoordinate_restrict_curve_eq_withDensity hab hγ hcoord,
    integral_withDensity_eq_integral_toReal_smul
      (measurable_deriv γ |>.norm |>.ennreal_ofReal)
      (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (norm_nonneg _), smul_eq_mul]
  rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
  apply setIntegral_congr_fun measurableSet_Icc
  intro x hx
  dsimp only
  rw [hceq x hx]

end MeasureTheory
