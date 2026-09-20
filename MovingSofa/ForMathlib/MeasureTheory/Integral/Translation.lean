import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.WithDensity

noncomputable section

open MeasureTheory Set
open scoped ENNReal Topology

namespace MeasureTheory

/-- Translation of a measurable real set preserves integrals. -/
theorem integral_image_add_right_eq (c : ℝ) (E : Set ℝ) (hE : MeasurableSet E)
    (f : ℝ → ℝ) :
    (∫ y in (fun x : ℝ ↦ x + c) '' E, f y) = ∫ x in E, f (x + c) := by
  let φ : ℝ → ℝ := fun x ↦ x + c
  have hφ : MeasurableEmbedding φ :=
    (Homeomorph.addRight c).isClosedEmbedding.measurableEmbedding
  have hpres : MeasurePreserving φ volume volume :=
    ⟨hφ.measurable, map_add_right_eq_self volume c⟩
  have himage : MeasurableSet (φ '' E) := hφ.measurableSet_image' hE
  have hpre : φ ⁻¹' (φ '' E) = E := Set.preimage_image_eq E hφ.injective
  have hr := hpres.restrict_preimage himage
  rw [hpre] at hr
  exact (hr.integral_comp hφ f).symm

/-- Translating both endpoints of a closed real interval translates the integrand. -/
theorem integral_Icc_const_add_eq (c a b : ℝ) (f : ℝ → ℝ) :
    (∫ y in Icc (c + a) (c + b), f y) = ∫ x in Icc a b, f (x + c) := by
  rw [show c + a = a + c from add_comm c a, show c + b = b + c from add_comm c b,
    ← Set.image_add_const_Icc, integral_image_add_right_eq c _ measurableSet_Icc]

/-- Integrability on a translated measurable set is preserved by translation. -/
theorem integrableOn_comp_add_right_iff (c : ℝ) (E : Set ℝ) (hE : MeasurableSet E)
    (f : ℝ → ℝ) :
    IntegrableOn (fun x ↦ f (x + c)) E ↔
      IntegrableOn f ((fun x : ℝ ↦ x + c) '' E) := by
  let φ : ℝ → ℝ := fun x ↦ x + c
  have hφ : MeasurableEmbedding φ :=
    (Homeomorph.addRight c).isClosedEmbedding.measurableEmbedding
  have hpres : MeasurePreserving φ volume volume :=
    ⟨hφ.measurable, map_add_right_eq_self volume c⟩
  have himage : MeasurableSet (φ '' E) := hφ.measurableSet_image' hE
  have hpre : φ ⁻¹' (φ '' E) = E := Set.preimage_image_eq E hφ.injective
  have hr := hpres.restrict_preimage himage
  rw [hpre] at hr
  exact hr.integrable_comp_emb hφ

/-- A lower Lebesgue integral of a right-translated function is the integral of the function
itself over the translated set. -/
theorem setLIntegral_comp_sub_right (w : ℝ → ℝ≥0∞) (c : ℝ) (A : Set ℝ) :
    ∫⁻ u in A, w (u - c) = ∫⁻ t in (fun t : ℝ ↦ t + c) ⁻¹' A, w t := by
  have hemb : MeasurableEmbedding fun t : ℝ ↦ t + c :=
    (MeasurableEquiv.addRight c).measurableEmbedding
  simpa using ((measurePreserving_add_right (volume : Measure ℝ) c).setLIntegral_comp_preimage_emb
    hemb (fun u ↦ w (u - c)) A).symm

/-- Pushing a weighted restriction of Lebesgue measure forward along `t ↦ t + c` translates both
the set and the weight. -/
theorem map_add_right_restrict_withDensity (c : ℝ) (S : Set ℝ) (w : ℝ → ℝ≥0∞) :
    Measure.map (fun t : ℝ ↦ t + c) ((volume.restrict S).withDensity w) =
      (volume.restrict ((fun t : ℝ ↦ t + c) '' S)).withDensity (fun u ↦ w (u - c)) := by
  have hemb : MeasurableEmbedding fun t : ℝ ↦ t + c :=
    (MeasurableEquiv.addRight c).measurableEmbedding
  ext A hA
  have hpre : MeasurableSet ((fun t : ℝ ↦ t + c) ⁻¹' A) := hA.preimage hemb.measurable
  rw [Measure.map_apply hemb.measurable hA, withDensity_apply _ hpre,
    Measure.restrict_restrict hpre, withDensity_apply _ hA, Measure.restrict_restrict hA,
    setLIntegral_comp_sub_right, Set.preimage_inter, hemb.injective.preimage_image]

end MeasureTheory
