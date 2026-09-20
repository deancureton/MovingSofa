import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Set

noncomputable section

namespace MeasureTheory

/-- A finite sum of atomic contributions is bounded by the integral of a nonnegative function. -/
theorem sum_measureReal_mul_le_setIntegral {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (μ : MeasureTheory.Measure α) (D : Finset α)
    {E : Set α} {f : α → ℝ} (hE : MeasurableSet E)
    (hDE : (D : Set α) ⊆ E) (hf : MeasureTheory.IntegrableOn f E μ)
    (hnonneg : ∀ x ∈ E, 0 ≤ f x) :
    ∑ x ∈ D, (μ {x}).toReal * f x ≤ ∫ x in E, f x ∂μ := by
  have hfinite := MeasureTheory.setIntegral_finset D (hf.mono_set hDE)
  simp only [smul_eq_mul, MeasureTheory.measureReal_def] at hfinite
  rw [← hfinite]
  apply MeasureTheory.setIntegral_mono_set hf
  · exact (MeasureTheory.ae_restrict_iff' hE).mpr (Filter.Eventually.of_forall hnonneg)
  · exact Filter.Eventually.of_forall hDE

end MeasureTheory
