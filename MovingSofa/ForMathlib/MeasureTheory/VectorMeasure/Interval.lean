import Mathlib.MeasureTheory.VectorMeasure.WithDensity
import Mathlib.MeasureTheory.VectorMeasure.IntegrationByParts
import Mathlib.MeasureTheory.Integral.Bochner.Set

noncomputable section

open Set MeasureTheory

namespace MeasureTheory.VectorMeasure

/-- Agreement on half-open intervals and the whole space determines a vector measure. -/
theorem ext_of_Ioc {α E : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
    [SecondCountableTopology α] [MeasurableSpace α] [BorelSpace α]
    [NormedAddCommGroup E] (μ ν : VectorMeasure α E)
    (h : ∀ a b, a < b → μ (Ioc a b) = ν (Ioc a b))
    (huniv : μ univ = ν univ) : μ = ν := by
  apply ext_of_generateFrom {s | ∃ a b, a < b ∧ Ioc a b = s} _
    (BorelSpace.measurable_eq.trans (borel_eq_generateFrom_Ioc α))
    (isPiSystem_Ioc id id) huniv
  rintro s ⟨a, b, hab, rfl⟩
  exact h a b hab

end MeasureTheory.VectorMeasure

/-- Pulling an integrable density back along a measurable embedding gives its image integrals. -/
theorem MeasurableEmbedding.exists_vectorMeasure_image_integral
    {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : α → β} (hf : MeasurableEmbedding f) (μ : Measure β) (g : β → E)
    (hg : Integrable g μ) :
    ∃ ν : VectorMeasure α E, ∀ s, MeasurableSet s → ν s = ∫ x in f '' s, g x ∂μ := by
  have hi : Integrable (fun x ↦ g (f x)) (μ.comap f) := by
    apply hf.integrable_map_iff.mp
    rw [hf.map_comap]
    exact hg.integrableOn
  refine ⟨(μ.comap f).withDensityᵥ (fun x ↦ g (f x)), ?_⟩
  intro s hs
  rw [withDensityᵥ_apply hi hs]
  have h := hf.setIntegral_map (μ := μ.comap f) g (f '' s)
  rw [hf.map_comap, hf.injective.preimage_image,
    Measure.restrict_restrict_of_subset (image_subset_range _ _)] at h
  exact h.symm
