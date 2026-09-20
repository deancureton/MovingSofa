import MovingSofa.ForMathlib.MeasureTheory.StieltjesDensity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import MovingSofa.Analysis.Stieltjes.Integral
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous

noncomputable section

open MeasureTheory Set

namespace MovingSofa

def stieltjesScalarExtension {a b : ℝ} (f : RightContinuousIntervalBV a b)
    (t : ℝ) : ℝ := by
  classical
  exact if h : t ∈ Set.Icc a b then f.toFun ⟨t, h⟩ else 0

def HasIntervalStieltjesDensity {a b : ℝ} (f : RightContinuousIntervalBV a b)
    (r : ℝ → ℝ) : Prop :=
  Integrable r (volume.restrict (Set.Icc a b)) ∧
    ∀ E : Set ℝ, MeasurableSet E →
      intervalStieltjesMeasure f {t | (t : ℝ) ∈ E} =
        ∫ t in E, r t ∂volume.restrict (Set.Icc a b)

theorem intervalStieltjesMeasure_Ioc {a b : ℝ}
    (f : RightContinuousIntervalBV a b) (c d : Set.Icc a b) (hcd : c ≤ d) :
    intervalStieltjesMeasure f (Set.Ioc c d) = f.toFun d - f.toFun c := by
  rw [intervalStieltjesMeasure, f.boundedVariation.vectorMeasure_Ioc hcd]
  rw [f.right_continuous d |>.rightLim_eq, f.right_continuous c |>.rightLim_eq]

private theorem stieltjesScalarExtension_eq_add_integral {a b : ℝ} (hab : a ≤ b)
    (f : RightContinuousIntervalBV a b) (r : ℝ → ℝ)
    (hr : HasIntervalStieltjesDensity f r) (t : Set.Icc a b) :
    stieltjesScalarExtension f (t : ℝ) =
      f.toFun ⟨a, le_rfl, hab⟩ + ∫ x in a..(t : ℝ), r x := by
  have hinc := hr.2 (Ioc a (t : ℝ)) measurableSet_Ioc
  have hset : {x : Icc a b | (x : ℝ) ∈ Ioc a (t : ℝ)} =
      Ioc (⟨a, le_rfl, hab⟩ : Icc a b) t := rfl
  rw [hset, intervalStieltjesMeasure_Ioc f _ _ t.property.1] at hinc
  have hmeasure :
      (volume.restrict (Set.Icc a b)).restrict (Set.Ioc a (t : ℝ)) =
        volume.restrict (Set.Ioc a (t : ℝ)) := by
    exact Measure.restrict_restrict_of_subset
      (fun x hx ↦ ⟨hx.1.le, hx.2.trans t.property.2⟩)
  have hrestrict :
      (∫ x in Set.Ioc a (t : ℝ), r x ∂volume.restrict (Set.Icc a b)) =
        ∫ x in Set.Ioc a (t : ℝ), r x := by
    rw [hmeasure]
  rw [stieltjesScalarExtension]
  simp only [dite_eq_left t.2]
  change f.toFun t = _
  rw [intervalIntegral.integral_of_le t.2.1]
  have hinc' := hinc.trans hrestrict
  linarith

private theorem absolutelyContinuousOnInterval_of_stieltjesDensity {a b : ℝ} (hab : a ≤ b)
    (f : RightContinuousIntervalBV a b) (r : ℝ → ℝ)
    (hr : HasIntervalStieltjesDensity f r) :
    AbsolutelyContinuousOnInterval (stieltjesScalarExtension f) a b := by
  have hri : IntervalIntegrable r volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2 hr.1
  have hp := hri.absolutelyContinuousOnInterval_intervalIntegral
    (c := a) (by simp [hab])
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ ↦ f.toFun ⟨a, le_rfl, hab⟩) a b :=
    (LipschitzWith.const _).lipschitzOnWith.absolutelyContinuousOnInterval
  have hs := hc.add hp
  apply hs.congr
  intro x hx
  have hx' : x ∈ Set.Icc a b := by
    simpa [Set.uIcc_of_le hab] using hx
  have hprim := stieltjesScalarExtension_eq_add_integral hab f r hr ⟨x, hx'⟩
  simpa [stieltjesScalarExtension, hx'] using hprim.symm

private theorem ae_hasDerivAt_of_stieltjesDensity {a b : ℝ} (hab : a ≤ b)
    (f : RightContinuousIntervalBV a b) (r : ℝ → ℝ)
    (hr : HasIntervalStieltjesDensity f r) :
    ∀ᵐ t ∂volume.restrict (Set.Ioo a b),
      HasDerivAt (stieltjesScalarExtension f) (r t) t := by
  have hri : IntervalIntegrable r volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2 hr.1
  have hder := IntervalIntegrable.ae_hasDerivAt_integral hri
  refine (ae_restrict_iff' measurableSet_Ioo).2 ?_
  filter_upwards [hder] with x hx hxo
  have hxu : x ∈ Set.uIcc a b := by
    simpa [Set.uIcc_of_le hab] using ⟨hxo.1.le, hxo.2.le⟩
  have hd := hx hxu a (by simp [hab])
  have hd' := hd.const_add (f.toFun ⟨a, le_rfl, hab⟩)
  apply hd'.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hxo] with y hyo
  have hycc : y ∈ Set.Icc a b := ⟨hyo.1.le, hyo.2.le⟩
  have hprim := stieltjesScalarExtension_eq_add_integral hab f r hr ⟨y, hycc⟩
  simpa [stieltjesScalarExtension, hycc] using hprim

private theorem intervalStieltjes_hasDensity_deriv {a b : ℝ} (hab : a ≤ b)
    (f : RightContinuousIntervalBV a b)
    (hf : AbsolutelyContinuousOnInterval (stieltjesScalarExtension f) a b) :
    HasIntervalStieltjesDensity f (deriv (stieltjesScalarExtension f)) := by
  let g := stieltjesScalarExtension f
  have hr : IntegrableOn (deriv g) (Icc a b) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hf.intervalIntegrable_deriv
  have hsub : Continuous f.toFun := by
    have h := (continuousOn_iff_continuous_domRestrict).mp
      (show ContinuousOn g (Icc a b) by simpa only [uIcc_of_le hab] using hf.continuousOn)
    convert h using 1
    funext x
    simp [g, stieltjesScalarExtension, x.property]
  have hri : Integrable (fun x : Icc a b ↦ deriv g x)
      (volume.comap (Subtype.val : Icc a b → ℝ)) :=
    (integrableOn_iff_comap_subtypeVal measurableSet_Icc).mp hr
  have hmeasure : intervalStieltjesMeasure f =
      (volume.comap (Subtype.val : Icc a b → ℝ)).withDensityᵥ
        (fun x : Icc a b ↦ deriv g x) := by
    apply f.boundedVariation.vectorMeasure_eq_withDensity_of_integral_Icc hsub hri
    intro c d hcd
    have hinc := (hf.mono (show uIcc (c : ℝ) (d : ℝ) ⊆ uIcc a b by
      rw [uIcc_of_le (show (c : ℝ) ≤ d from hcd), uIcc_of_le hab]
      exact Icc_subset_Icc c.property.1 d.property.2)).integral_deriv_eq_sub
    have hset : Icc c d = {x : Icc a b | (x : ℝ) ∈ Icc (c : ℝ) (d : ℝ)} := rfl
    rw [hset, integral_subtype_preimage measurableSet_Icc measurableSet_Icc]
    rw [Measure.restrict_restrict_of_subset (Icc_subset_Icc c.property.1 d.property.2),
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hcd, hinc]
    simp [stieltjesScalarExtension, c.property, d.property]
  refine ⟨hr, ?_⟩
  intro E hE
  have hpre : MeasurableSet {t : Icc a b | (t : ℝ) ∈ E} :=
    hE.preimage measurable_subtype_coe
  rw [hmeasure, withDensityᵥ_apply hri hpre,
    integral_subtype_preimage measurableSet_Icc hE]


theorem intervalStieltjes_absoluteContinuity (a b : ℝ) (hab : a ≤ b)
    (f : RightContinuousIntervalBV a b) :
    (AbsolutelyContinuousOnInterval (stieltjesScalarExtension f) a b ↔
      ∃ r : ℝ → ℝ, HasIntervalStieltjesDensity f r) ∧
    (∀ r : ℝ → ℝ, HasIntervalStieltjesDensity f r →
      ∀ᵐ t ∂volume.restrict (Set.Ioo a b),
        HasDerivAt (stieltjesScalarExtension f) (r t) t) := by
  refine ⟨⟨?_, ?_⟩, fun r hr ↦ ae_hasDerivAt_of_stieltjesDensity hab f r hr⟩
  · intro hf
    exact ⟨deriv (stieltjesScalarExtension f), intervalStieltjes_hasDensity_deriv hab f hf⟩
  · rintro ⟨r, hr⟩
    exact absolutelyContinuousOnInterval_of_stieltjesDensity hab f r hr

end MovingSofa
