import Mathlib.MeasureTheory.VectorMeasure.IntegrationByParts
import Mathlib.MeasureTheory.VectorMeasure.WithDensity

open MeasureTheory Set

/-- Equality of interval increments identifies a continuous BV function's vector measure. -/
theorem BoundedVariationOn.vectorMeasure_eq_withDensity_of_integral_Icc
    {α E : Type*} [LinearOrder α] [DenselyOrdered α] [TopologicalSpace α] [OrderTopology α]
    [SecondCountableTopology α] [MeasurableSpace α] [BorelSpace α]
    [CompactIccSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f r : α → E} {μ : Measure α} (hf : BoundedVariationOn f univ)
    (hcont : Continuous f) (hr : Integrable r μ)
    (hinc : ∀ a b, a ≤ b → f b - f a = ∫ x in Icc a b, r x ∂μ) :
    hf.vectorMeasure = μ.withDensityᵥ r := by
  apply VectorMeasure.ext_of_Icc
  intro a b hab
  rw [hf.vectorMeasure_Icc hab, (hcont.continuousAt (x := b)).continuousWithinAt.rightLim_eq,
    (hcont.continuousAt (x := a)).continuousWithinAt.leftLim_eq,
    withDensityᵥ_apply hr measurableSet_Icc]
  exact hinc a b hab

/-- Integrating on a subtype and a measurable preimage agrees with restricting both sets. -/
theorem MeasureTheory.integral_subtype_preimage {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s t : Set α} (hs : MeasurableSet s) (ht : MeasurableSet t) (f : α → E) :
    (∫ x in {x : s | (x : α) ∈ t}, f (x : α) ∂μ.comap Subtype.val) =
      ∫ x in t, f x ∂μ.restrict s := by
  have hpre : MeasurableSet {x : s | (x : α) ∈ t} := ht.preimage measurable_subtype_coe
  rw [← integral_indicator (μ := μ.comap (Subtype.val : s → α))
    (f := fun x : s ↦ f (x : α)) hpre]
  change (∫ x : s, (t.indicator f) (x : α) ∂μ.comap Subtype.val) = _
  rw [integral_subtype_comap hs, integral_indicator ht]
