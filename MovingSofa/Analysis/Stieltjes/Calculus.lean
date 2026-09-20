import MovingSofa.Analysis.Stieltjes.Integral
import MovingSofa.ForMathlib.MeasureTheory.VectorMeasure.WithDensity
import Mathlib.Analysis.BoundedVariation
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.RadonNikodym

noncomputable section

open Filter MeasureTheory
open scoped Topology

namespace MovingSofa

theorem intervalStieltjes_integration_by_parts (a b : ℝ) (hab : a ≤ b)
    (f g : RightContinuousIntervalBV a b) :
    ∃ left : Set.Icc a b → ℝ,
      (∀ t : Set.Icc a b, a < (t : ℝ) →
        Tendsto f.toFun (nhdsWithin t (Set.Iio t)) (𝓝 (left t))) ∧
      intervalStieltjesIntegral f g.toFun {t | a < (t : ℝ)} +
        intervalStieltjesIntegral g left {t | a < (t : ℝ)} =
      f.toFun ⟨b, hab, le_rfl⟩ * g.toFun ⟨b, hab, le_rfl⟩ -
        f.toFun ⟨a, le_rfl, hab⟩ * g.toFun ⟨a, le_rfl, hab⟩ := by
  let a' : Set.Icc a b := ⟨a, le_rfl, hab⟩
  let b' : Set.Icc a b := ⟨b, hab, le_rfl⟩
  refine ⟨Function.leftLim f.toFun, fun t _ ↦ f.boundedVariation.tendsto_leftLim t, ?_⟩
  have hfa (t : Set.Icc a b) : Function.rightLim f.toFun t = f.toFun t :=
    (f.right_continuous t).rightLim_eq
  have hga (t : Set.Icc a b) : Function.rightLim g.toFun t = g.toFun t :=
    (g.right_continuous t).rightLim_eq
  have hparts := BoundedVariationOn.setIntegral_Ioc_leftLim_vectorMeasure_eq_sub
    (B := ContinuousLinearMap.mul ℝ ℝ) f.boundedVariation g.boundedVariation (show a' ≤ b' by
      exact hab)
  have hset : {t : Set.Icc a b | a < (t : ℝ)} = Set.Ioc a' b' := by
    ext t
    constructor
    · intro ht
      exact ⟨ht, t.property.2⟩
    · exact fun ht ↦ ht.1
  have hmulflip : (ContinuousLinearMap.mul ℝ ℝ).flip = ContinuousLinearMap.mul ℝ ℝ := by
    ext
    simp
  rw [hmulflip] at hparts
  rw [hset]
  unfold intervalStieltjesIntegral intervalStieltjesMeasure
  change (∫ᵛ t in Set.Ioc a' b', g.toFun t
      ∂[ContinuousLinearMap.mul ℝ ℝ; f.boundedVariation.vectorMeasure]) +
    (∫ᵛ t in Set.Ioc a' b', Function.leftLim f.toFun t
      ∂[ContinuousLinearMap.mul ℝ ℝ; g.boundedVariation.vectorMeasure]) = _
  rw [hparts]
  simp only [hfa, hga]
  change _ + (f.toFun b' * g.toFun b' - f.toFun a' * g.toFun a' - _) = _
  dsimp [a', b']
  ring

/-- Stieltjes integration by parts on the open interval `(a, b)`: no endpoint atom is included
at `b`, and none is introduced at `a`. The left limit in the first integrand accounts for
simultaneous jumps. -/
theorem intervalStieltjes_integration_by_parts_Ioo (a b : ℝ) (hab : a < b)
    (f g : RightContinuousIntervalBV a b) :
    intervalStieltjesIntegral g (Function.leftLim f.toFun)
        {t | a < (t : ℝ) ∧ (t : ℝ) < b} +
      intervalStieltjesIntegral f g.toFun {t | a < (t : ℝ) ∧ (t : ℝ) < b} =
      Function.leftLim f.toFun ⟨b, hab.le, le_rfl⟩ *
          Function.leftLim g.toFun ⟨b, hab.le, le_rfl⟩ -
        f.toFun ⟨a, le_rfl, hab.le⟩ * g.toFun ⟨a, le_rfl, hab.le⟩ := by
  have hfa (t : Set.Icc a b) : Function.rightLim f.toFun t = f.toFun t :=
    (f.right_continuous t).rightLim_eq
  have hga (t : Set.Icc a b) : Function.rightLim g.toFun t = g.toFun t :=
    (g.right_continuous t).rightLim_eq
  have hparts := BoundedVariationOn.setIntegral_Ioo_leftLim_vectorMeasure_eq_sub
    (B := ContinuousLinearMap.mul ℝ ℝ) f.boundedVariation g.boundedVariation
    (show (⟨a, le_rfl, hab.le⟩ : Set.Icc a b) < ⟨b, hab.le, le_rfl⟩ from hab)
  have hset : {t : Set.Icc a b | a < (t : ℝ) ∧ (t : ℝ) < b} =
      Set.Ioo (⟨a, le_rfl, hab.le⟩ : Set.Icc a b) ⟨b, hab.le, le_rfl⟩ := by
    ext t
    exact ⟨fun ht ↦ ⟨ht.1, ht.2⟩, fun ht ↦ ⟨ht.1, ht.2⟩⟩
  have hmulflip : (ContinuousLinearMap.mul ℝ ℝ).flip = ContinuousLinearMap.mul ℝ ℝ := by
    ext
    simp
  rw [hmulflip] at hparts
  rw [hset]
  unfold intervalStieltjesIntegral intervalStieltjesMeasure
  rw [hparts]
  simp only [hfa, hga, ContinuousLinearMap.mul_apply']
  ring

theorem intervalStieltjes_product (a b : ℝ) (hab : a ≤ b)
    (f g : RightContinuousIntervalBV a b)
    (hcont : Continuous f.toFun ∨ Continuous g.toFun) :
    ∃ h : RightContinuousIntervalBV a b,
      (∀ t, h.toFun t = f.toFun t * g.toFun t) ∧
      ∀ E : Set (Set.Icc a b), MeasurableSet E →
        intervalStieltjesMeasure h E =
          intervalStieltjesIntegral f g.toFun E + intervalStieltjesIntegral g f.toFun E := by
  let h : RightContinuousIntervalBV a b :=
    ⟨fun t ↦ f.toFun t * g.toFun t,
      f.boundedVariation.bilinear_comp g.boundedVariation (ContinuousLinearMap.mul ℝ ℝ),
      fun t ↦ (f.right_continuous t).mul (g.right_continuous t)⟩
  refine ⟨h, fun _ ↦ rfl, fun E _ ↦ ?_⟩
  have hflip : (ContinuousLinearMap.mul ℝ ℝ).flip = ContinuousLinearMap.mul ℝ ℝ := by
    ext
    simp
  have hfr : Function.rightLim f.toFun = f.toFun :=
    funext fun t ↦ (f.right_continuous t).rightLim_eq
  have hgr : Function.rightLim g.toFun = g.toFun :=
    funext fun t ↦ (g.right_continuous t).rightLim_eq
  rcases hcont with hf | hg
  · have hfl : Function.leftLim f.toFun = f.toFun :=
      funext fun t ↦ hf.continuousAt.continuousWithinAt.leftLim_eq
    have hp := f.boundedVariation.setIntegral_leftLim_vectorMeasure_eq_sub
      (B := ContinuousLinearMap.mul ℝ ℝ) g.boundedVariation (s := E)
    rw [hflip, hfl, hgr] at hp
    change _ = _ + _
    unfold intervalStieltjesIntegral intervalStieltjesMeasure
    change (f.boundedVariation.bilinear_comp g.boundedVariation
      (ContinuousLinearMap.mul ℝ ℝ)).vectorMeasure E = _
    linarith
  · have hgl : Function.leftLim g.toFun = g.toFun :=
      funext fun t ↦ hg.continuousAt.continuousWithinAt.leftLim_eq
    have hp := f.boundedVariation.setIntegral_rightLim_vectorMeasure_eq_sub
      (B := ContinuousLinearMap.mul ℝ ℝ) g.boundedVariation (s := E)
    rw [hflip, hfr, hgl] at hp
    unfold intervalStieltjesIntegral intervalStieltjesMeasure
    change (f.boundedVariation.bilinear_comp g.boundedVariation
      (ContinuousLinearMap.mul ℝ ℝ)).vectorMeasure E = _
    linarith

/-- The integrated Stieltjes product rule: a bounded measurable weight distributes over the
Lebesgue–Stieltjes measure of a product one factor of which is continuous. -/
theorem intervalStieltjesIntegral_product_of_bounded {a b : ℝ} (hab : a ≤ b)
    (f g h : RightContinuousIntervalBV a b) (hgc : Continuous g.toFun)
    (hh : ∀ t, h.toFun t = f.toFun t * g.toFun t)
    (φ : Set.Icc a b → ℝ) (hφ : Measurable φ) (C : ℝ) (hφb : ∀ t, ‖φ t‖ ≤ C)
    (E : Set (Set.Icc a b)) (hE : MeasurableSet E) :
    intervalStieltjesIntegral h φ E =
      intervalStieltjesIntegral f (fun t ↦ φ t * g.toFun t) E +
        intervalStieltjesIntegral g (fun t ↦ φ t * f.toFun t) E := by
  obtain ⟨h', hh', hh'm⟩ := intervalStieltjes_product a b hab f g (Or.inr hgc)
  have hheq : h = h' :=
    RightContinuousIntervalBV.toFun_injective (funext fun t ↦ (hh t).trans (hh' t).symm)
  obtain ⟨Cf, hCf⟩ := f.exists_norm_bound hab
  obtain ⟨Cg, hCg⟩ := g.exists_norm_bound hab
  have hfm : Measurable f.toFun := f.boundedVariation.measurable
  have hgm : Measurable g.toFun := g.boundedVariation.measurable
  -- both Stieltjes measures are absolutely continuous over the sum of their total variations
  set ρ : Measure (Set.Icc a b) := (intervalStieltjesMeasure f).totalVariation +
    (intervalStieltjesMeasure g).totalVariation with hρ
  have _ : IsFiniteMeasure ρ := by rw [hρ]; infer_instance
  have hac : ∀ μ : SignedMeasure (Set.Icc a b), μ.totalVariation ≤ ρ →
      μ ≪ᵥ ρ.toENNRealVectorMeasure := fun μ hle ↦ by
    rw [SignedMeasure.absolutelyContinuous_ennreal_iff,
      VectorMeasure.ennrealToMeasure_toENNRealVectorMeasure]
    exact Measure.absolutelyContinuous_of_le hle
  have hacf := hac (intervalStieltjesMeasure f) (by rw [hρ]; exact Measure.le_add_right le_rfl)
  have hacg := hac (intervalStieltjesMeasure g) (by rw [hρ]; exact Measure.le_add_left le_rfl)
  set rf : Set.Icc a b → ℝ := (intervalStieltjesMeasure f).rnDeriv ρ with hrf
  set rg : Set.Icc a b → ℝ := (intervalStieltjesMeasure g).rnDeriv ρ with hrg
  have hrfi : Integrable rf ρ := SignedMeasure.integrable_rnDeriv _ ρ
  have hrgi : Integrable rg ρ := SignedMeasure.integrable_rnDeriv _ ρ
  have hμf : ρ.withDensityᵥ rf = intervalStieltjesMeasure f :=
    SignedMeasure.withDensityᵥ_rnDeriv_eq _ ρ hacf
  have hμg : ρ.withDensityᵥ rg = intervalStieltjesMeasure g :=
    SignedMeasure.withDensityᵥ_rnDeriv_eq _ ρ hacg
  have hgrf : Integrable (fun x ↦ g.toFun x * rf x) ρ :=
    hrfi.bdd_mul hgm.aestronglyMeasurable (Filter.Eventually.of_forall hCg)
  have hfrg : Integrable (fun x ↦ f.toFun x * rg x) ρ :=
    hrgi.bdd_mul hfm.aestronglyMeasurable (Filter.Eventually.of_forall hCf)
  have hsumi : Integrable (fun x ↦ g.toFun x * rf x + f.toFun x * rg x) ρ := hgrf.add hfrg
  have hφg : Measurable fun t ↦ φ t * g.toFun t := hφ.mul hgm
  have hφf : Measurable fun t ↦ φ t * f.toFun t := hφ.mul hfm
  -- the product measure is the density of the two-term Radon–Nikodym sum
  have hsum : intervalStieltjesMeasure h =
      ρ.withDensityᵥ (fun x ↦ g.toFun x * rf x + f.toFun x * rg x) := by
    rw [hheq]
    ext S hS
    rw [withDensityᵥ_apply hsumi hS, hh'm S hS]
    have h1 : intervalStieltjesIntegral f g.toFun S = ∫ x in S, g.toFun x * rf x ∂ρ := by
      rw [intervalStieltjesIntegral, ← hμf,
        VectorMeasure.setIntegral_withDensity_mul_of_bounded hrfi
          hgm.aestronglyMeasurable Cg hCg S hS]
    have h2 : intervalStieltjesIntegral g f.toFun S = ∫ x in S, f.toFun x * rg x ∂ρ := by
      rw [intervalStieltjesIntegral, ← hμg,
        VectorMeasure.setIntegral_withDensity_mul_of_bounded hrgi
          hfm.aestronglyMeasurable Cf hCf S hS]
    rw [h1, h2, integral_add hgrf.integrableOn hfrg.integrableOn]
  have hb1 : ∀ x, ‖φ x * g.toFun x‖ ≤ C * Cg := fun x ↦ by
    rw [norm_mul]
    exact mul_le_mul (hφb x) (hCg x) (norm_nonneg _) ((norm_nonneg _).trans (hφb x))
  have hb2 : ∀ x, ‖φ x * f.toFun x‖ ≤ C * Cf := fun x ↦ by
    rw [norm_mul]
    exact mul_le_mul (hφb x) (hCf x) (norm_nonneg _) ((norm_nonneg _).trans (hφb x))
  have hi1 : Integrable (fun x ↦ φ x * g.toFun x * rf x) ρ :=
    hrfi.bdd_mul hφg.aestronglyMeasurable (Filter.Eventually.of_forall hb1)
  have hi2 : Integrable (fun x ↦ φ x * f.toFun x * rg x) ρ :=
    hrgi.bdd_mul hφf.aestronglyMeasurable (Filter.Eventually.of_forall hb2)
  rw [show intervalStieltjesIntegral h φ E =
      ∫ x in E, φ x * (g.toFun x * rf x + f.toFun x * rg x) ∂ρ by
    rw [intervalStieltjesIntegral, hsum,
      VectorMeasure.setIntegral_withDensity_mul_of_bounded hsumi
        hφ.aestronglyMeasurable C hφb E hE],
    show intervalStieltjesIntegral f (fun t ↦ φ t * g.toFun t) E =
      ∫ x in E, φ x * g.toFun x * rf x ∂ρ by
    rw [intervalStieltjesIntegral, ← hμf,
      VectorMeasure.setIntegral_withDensity_mul_of_bounded hrfi
        hφg.aestronglyMeasurable (C * Cg) hb1 E hE],
    show intervalStieltjesIntegral g (fun t ↦ φ t * f.toFun t) E =
      ∫ x in E, φ x * f.toFun x * rg x ∂ρ by
    rw [intervalStieltjesIntegral, ← hμg,
      VectorMeasure.setIntegral_withDensity_mul_of_bounded hrgi
        hφf.aestronglyMeasurable (C * Cf) hb2 E hE],
    ← integral_add hi1.integrableOn hi2.integrableOn]
  exact setIntegral_congr_fun hE fun x _ ↦ by ring

end MovingSofa
