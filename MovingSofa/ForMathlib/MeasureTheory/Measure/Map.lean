import Mathlib.MeasureTheory.Measure.Map

namespace MeasureTheory.Measure

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α}

/-- If `g` is almost everywhere a left inverse of `f`, then pushing a measure forward along `f`
and then along `g` recovers it. This is the almost-everywhere form of
`MeasurableEquiv.map_symm_map`. -/
theorem map_map_of_ae_leftInverse {f : α → β} (hf : Measurable f) {g : β → α}
    (hg : Measurable g) (h : ∀ᵐ a ∂μ, g (f a) = a) :
    (μ.map f).map g = μ := by
  rw [map_map hg hf, show μ.map (g ∘ f) = μ.map id from map_congr h, map_id]

end MeasureTheory.Measure
