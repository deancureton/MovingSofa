import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Map

open Set
open scoped ENNReal

namespace MeasureTheory.Measure

/-- An injective image of a weighted restriction preserves null singleton masses. -/
theorem map_restrict_withDensity_singleton {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSingletonClass β]
    (μ : Measure α) [NullSingletonClass μ] (f : α → β) (hf : Measurable f)
    (s : Set α) (hinj : Set.InjOn f s) (w : α → ℝ≥0∞) {x : α} (hx : x ∈ s) :
    Measure.map f ((μ.restrict s).withDensity w) {f x} = 0 := by
  rw [Measure.map_apply hf (measurableSet_singleton _)]
  apply withDensity_absolutelyContinuous
  rw [Measure.restrict_apply (hf (measurableSet_singleton _))]
  have heq : f ⁻¹' {f x} ∩ s = {x} := by
    ext y
    simp only [mem_inter_iff, mem_preimage, mem_singleton_iff]
    exact ⟨fun h ↦ hinj h.2 hx h.1, fun h ↦ by subst y; exact ⟨rfl, hx⟩⟩
  rw [heq, measure_singleton]

/-- Pushing a weighted measure forward along a measurable map is linear in the weight: if `w` is
the pointwise combination `a * w₁ + b * w₂`, then the pushforward of `μ.withDensity w` is the
same combination of the pushforwards of `μ.withDensity w₁` and `μ.withDensity w₂`. -/
theorem map_withDensity_eq_smul_add_smul {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) {φ : α → β} (hφ : Measurable φ) (a b : ℝ≥0∞) {w w₁ w₂ : α → ℝ≥0∞}
    (h₁ : Measurable w₁) (h₂ : Measurable w₂) (hw : ∀ x, w x = a * w₁ x + b * w₂ x) :
    Measure.map φ (μ.withDensity w) =
      a • Measure.map φ (μ.withDensity w₁) + b • Measure.map φ (μ.withDensity w₂) := by
  have hwfun : w = a • w₁ + b • w₂ := funext hw
  rw [hwfun, withDensity_add_left (h₁.const_smul a), withDensity_smul _ h₁,
    withDensity_smul _ h₂, Measure.map_add _ _ hφ, Measure.map_smul _ hφ.aemeasurable,
    Measure.map_smul _ hφ.aemeasurable]

end MeasureTheory.Measure
