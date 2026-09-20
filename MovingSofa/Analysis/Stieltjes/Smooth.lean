import MovingSofa.Analysis.Stieltjes.AbsoluteContinuity
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

noncomputable section

open MeasureTheory Set
open scoped Topology

namespace MovingSofa

/-- A continuously differentiable real function restricted to a compact interval, together with
its Stieltjes density. -/
theorem exists_intervalBV_of_hasDerivAt {a b : ℝ} (hab : a ≤ b)
    (φ φ' : ℝ → ℝ) (hderiv : ∀ t, HasDerivAt φ (φ' t) t) (hφ' : Continuous φ') :
    ∃ F : RightContinuousIntervalBV a b,
      (∀ t, F.toFun t = φ t) ∧ HasIntervalStieltjesDensity F φ' := by
  have hdiff : Differentiable ℝ φ := fun t ↦ (hderiv t).differentiableAt
  have hcontDiff : ContDiff ℝ 1 φ := by
    rw [contDiff_one_iff_deriv]
    refine ⟨hdiff, ?_⟩
    convert hφ' using 1
    funext t
    exact (hderiv t).deriv
  have hBVreal : BoundedVariationOn φ (Icc a b) := by
    simpa only [uIcc_of_le hab] using
      (hcontDiff.contDiffOn.absolutelyContinuousOnInterval (a := a) (b := b)).boundedVariationOn
  let ι : Icc a b → ℝ := (↑)
  have hBV : BoundedVariationOn (φ ∘ ι) Set.univ :=
    ne_top_of_le_ne_top hBVreal
      (eVariationOn.comp_le_of_monotoneOn φ ι
        (fun _ _ _ _ h ↦ h) (fun t _ ↦ t.property))
  let F : RightContinuousIntervalBV a b :=
    { toFun := φ ∘ ι
      boundedVariation := hBV
      right_continuous := fun t ↦
        (hderiv (t : ℝ)).continuousAt.comp_continuousWithinAt
          continuous_subtype_val.continuousWithinAt }
  have hφ'int : Integrable φ' (volume.restrict (Icc a b)) :=
    hφ'.continuousOn.integrableOn_compact isCompact_Icc
  have hsubtype : Integrable (fun t : Icc a b ↦ φ' t)
      (volume.comap (Subtype.val : Icc a b → ℝ)) :=
    (integrableOn_iff_comap_subtypeVal measurableSet_Icc).mp hφ'int
  have hmeasure : intervalStieltjesMeasure F =
      (volume.comap (Subtype.val : Icc a b → ℝ)).withDensityᵥ
        (fun t : Icc a b ↦ φ' t) := by
    apply F.boundedVariation.vectorMeasure_eq_withDensity_of_integral_Icc
    · exact (continuous_iff_continuousAt.2 fun t ↦ (hderiv t).continuousAt).comp
        continuous_subtype_val
    · exact hsubtype
    · intro c d hcd
      have hftc : ∫ x in (c : ℝ)..(d : ℝ), φ' x = φ d - φ c :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt
          (fun x _ ↦ hderiv x) (hφ'.intervalIntegrable (c : ℝ) (d : ℝ))
      have hset : Icc c d = {x : Icc a b | (x : ℝ) ∈ Icc (c : ℝ) (d : ℝ)} := rfl
      rw [hset, integral_subtype_preimage measurableSet_Icc measurableSet_Icc,
        Measure.restrict_restrict_of_subset
          (Icc_subset_Icc c.property.1 d.property.2)]
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hcd, hftc]
      simp [F, ι]
  refine ⟨F, fun _ ↦ rfl, hφ'int, ?_⟩
  intro E hE
  have hpre : MeasurableSet {t : Icc a b | (t : ℝ) ∈ E} :=
    hE.preimage measurable_subtype_coe
  rw [hmeasure, withDensityᵥ_apply hsubtype hpre,
    integral_subtype_preimage measurableSet_Icc hE]

/-- A right-continuous interval bounded-variation function that agrees on its interval with an
absolutely continuous function differentiable on the open interval has that derivative as its
Stieltjes density. Unlike `exists_intervalBV_of_hasDerivAt` this identifies the density of a
*given* bounded-variation function, and asks for differentiability only in the interior. -/
theorem hasIntervalStieltjesDensity_of_hasDerivAt {a b : ℝ} (hab : a ≤ b)
    (F : RightContinuousIntervalBV a b) (φ φ' : ℝ → ℝ)
    (hF : ∀ t : Icc a b, F.toFun t = φ t)
    (hac : AbsolutelyContinuousOnInterval φ a b)
    (hderiv : ∀ t ∈ Ioo a b, HasDerivAt φ (φ' t) t)
    (hint : IntegrableOn φ' (Icc a b)) :
    HasIntervalStieltjesDensity F φ' := by
  have hext : ∀ t ∈ Icc a b, stieltjesScalarExtension F t = φ t := by
    intro t ht
    rw [stieltjesScalarExtension, dite_eq_left ht]
    exact hF ⟨t, ht⟩
  have hac' : AbsolutelyContinuousOnInterval (stieltjesScalarExtension F) a b :=
    hac.congr fun t ht ↦ (hext t (by simpa only [uIcc_of_le hab] using ht)).symm
  obtain ⟨ρ, hρ⟩ := (intervalStieltjes_absoluteContinuity a b hab F).1.1 hac'
  have hIoo : ρ =ᵐ[volume.restrict (Ioo a b)] φ' := by
    filter_upwards [(intervalStieltjes_absoluteContinuity a b hab F).2 ρ hρ,
      ae_restrict_mem measurableSet_Ioo] with t ht htmem
    refine ht.unique ((hderiv t htmem).congr_of_eventuallyEq ?_)
    filter_upwards [isOpen_Ioo.mem_nhds htmem] with u hu
    exact hext u (Ioo_subset_Icc_self hu)
  have hIcc : ρ =ᵐ[volume.restrict (Icc a b)] φ' := by
    rwa [Measure.restrict_congr_set (MeasureTheory.Ioo_ae_eq_Icc (μ := volume))] at hIoo
  refine ⟨hint, fun E hE ↦ ?_⟩
  rw [hρ.2 E hE]
  exact integral_congr_ae (hIcc.filter_mono (ae_mono Measure.restrict_le_self))

end MovingSofa
