import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

noncomputable section

open Set

namespace MeasureTheory

/-- A membership that fails only on a countable set holds almost everywhere on the restriction
of a measure with null singletons. -/
theorem ae_restrict_mem_of_countable_diff {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [NullSingletonClass μ] {S A N : Set α} (hS : MeasurableSet S) (hN : N.Countable)
    (hsub : S \ A ⊆ N) : ∀ᵐ x ∂μ.restrict S, x ∈ A := by
  rw [ae_iff, Measure.restrict_apply' hS]
  exact measure_mono_null (fun x hx ↦ hsub ⟨hx.2, hx.1⟩) (hN.measure_zero μ)

/-- Along an injective parametrization, a finite-measure atom occurs only almost nowhere. -/
theorem ae_measure_singleton_comp_eq_zero_of_injOn
    {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (μ : Measure X) [SFinite μ] {s : Set ℝ} (hs : MeasurableSet s)
    {f : ℝ → X} (hf : Set.InjOn f s) :
    ∀ᵐ t ∂volume.restrict s, μ {f t} = 0 := by
  let A : Set X := {x | 0 < μ {x}}
  have hA : A.Countable := μ.countable_meas_level_set_pos measurable_id
  let B : Set ℝ := {t | t ∈ s ∧ f t ∈ A}
  have hmaps : MapsTo f B A := fun _ h ↦ h.2
  have hB : B.Countable := hmaps.countable_of_injOn (hf.mono fun _ h ↦ h.1) hA
  filter_upwards [ae_restrict_mem hs, hB.ae_notMem (volume.restrict s)] with t hts htB
  by_contra hne
  exact htB ⟨hts, pos_iff_ne_zero.mpr hne⟩

/-- A measure carried by a finite set is the sum of its atomic contributions. -/
theorem measure_eq_sum_singleton_inter_of_compl_eq_zero
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure α) (S : Finset α) (hS : μ (S : Set α)ᶜ = 0)
    (E : Set α) (hE : MeasurableSet E) :
    μ E = ∑ x ∈ S, μ ({x} ∩ E) := by
  classical
  have hae : ∀ᵐ x ∂μ, x ∈ (S : Set α) := by
    rw [ae_iff]
    exact hS
  have hrestrict : μ.restrict (S : Set α) = μ :=
    Measure.restrict_eq_self_of_ae_mem hae
  have hinter : μ E = μ (E ∩ (S : Set α)) := by
    calc
      μ E = (μ.restrict (S : Set α)) E := by rw [hrestrict]
      _ = μ (E ∩ (S : Set α)) := Measure.restrict_apply hE
  rw [hinter]
  have heq : E ∩ (S : Set α) = ⋃ x ∈ S, ({x} ∩ E : Set α) := by
    ext x
    simp [and_comm]
  rw [heq, measure_biUnion_finset]
  · intro i _ j _ hij
    simp only [Set.disjoint_left]
    intro x hxi hxj
    exact hij (hxi.1.symm.trans hxj.1)
  · intro b _
    exact (measurableSet_singleton b).inter hE

/-- A measure carried by the image of a finite index set is bounded by the sum of atomic bounds
over any index subset containing every index whose atom meets the measured set. -/
theorem measure_le_sum_of_measure_compl_image_eq_zero
    {α ι : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure α) (S S' : Finset ι) (f : ι → α) (b : ι → ENNReal)
    (hf : Set.InjOn f (S : Set ι)) (hS : μ (f '' (S : Set ι))ᶜ = 0)
    (hb : ∀ i ∈ S, μ {f i} ≤ b i) (E : Set α) (hE : MeasurableSet E)
    (hactive : ∀ i ∈ S, f i ∈ E → i ∈ S') :
    μ E ≤ ∑ i ∈ S', b i := by
  classical
  have himage : ((S.image f : Finset α) : Set α) = f '' (S : Set ι) := by
    ext x
    simp
  rw [measure_eq_sum_singleton_inter_of_compl_eq_zero μ (S.image f)
    (by rw [himage]; exact hS) E hE]
  calc
    ∑ x ∈ S.image f, μ ({x} ∩ E) = ∑ i ∈ S, μ ({f i} ∩ E) :=
      Finset.sum_image fun i hi j hj h ↦ hf (Finset.mem_coe.2 hi) (Finset.mem_coe.2 hj) h
    _ ≤ ∑ i ∈ S, (if f i ∈ E then b i else 0) := by
      refine Finset.sum_le_sum fun i hi ↦ ?_
      by_cases hfi : f i ∈ E
      · have hinter : ({f i} : Set α) ∩ E = {f i} := by
          ext y
          simp [hfi]
        simp only [hinter, hfi, ite_true]
        exact hb i hi
      · have hinter : ({f i} : Set α) ∩ E = ∅ := by
          ext y
          simp [hfi]
        simp [hinter, hfi]
    _ = ∑ i ∈ S.filter (fun i ↦ f i ∈ E), b i := (Finset.sum_filter _ _).symm
    _ ≤ ∑ i ∈ S', b i := by
      refine Finset.sum_le_sum_of_subset fun i hi ↦ ?_
      obtain ⟨hiS, hiE⟩ := Finset.mem_filter.1 hi
      exact hactive i hiS hiE

/-! ### Almost every point of a half-open interval is interior -/

/-- Almost every point of a half-open interval, for a measure with null singletons, lies in the
corresponding open interval. -/
theorem ae_restrict_Ico_mem_Ioo {μ : Measure ℝ} [NullSingletonClass μ] (a b : ℝ) :
    ∀ᵐ t ∂μ.restrict (Ico a b), t ∈ Ioo a b :=
  ae_restrict_mem_of_countable_diff measurableSet_Ico (countable_singleton a)
    fun _ ⟨hx, hx'⟩ ↦ mem_singleton_iff.2 (le_antisymm (not_lt.1 fun h ↦ hx' ⟨h, hx.2⟩) hx.1)

/-- Almost every point of a half-open interval, for a measure with null singletons, lies in the
corresponding open interval. -/
theorem ae_restrict_Ioc_mem_Ioo {μ : Measure ℝ} [NullSingletonClass μ] (a b : ℝ) :
    ∀ᵐ t ∂μ.restrict (Ioc a b), t ∈ Ioo a b :=
  ae_restrict_mem_of_countable_diff measurableSet_Ioc (countable_singleton b)
    fun _ ⟨hx, hx'⟩ ↦ mem_singleton_iff.2 (le_antisymm hx.2 (not_lt.1 fun h ↦ hx' ⟨hx.1, h⟩))

/-- Almost every point of a half-open interval, for a measure with null singletons, lies in one
of the two open intervals cut out by an arbitrary intermediate point. -/
theorem ae_restrict_Ico_mem_Ioo_union_Ioo {μ : Measure ℝ} [NullSingletonClass μ] (a b c : ℝ) :
    ∀ᵐ t ∂μ.restrict (Ico a c), t ∈ Ioo a b ∪ Ioo b c := by
  refine ae_restrict_mem_of_countable_diff measurableSet_Ico
    ((countable_singleton b).insert a) ?_
  rintro x ⟨hx, hx'⟩
  rcases lt_trichotomy x b with h | h | h
  · exact Or.inl (le_antisymm (not_lt.1 fun hlt ↦ hx' (Or.inl ⟨hlt, h⟩)) hx.1)
  · exact Or.inr (mem_singleton_iff.2 h)
  · exact absurd (Or.inr ⟨h, hx.2⟩) hx'

/-- Almost every point of a half-open interval, for a measure with null singletons, lies in one
of the two open intervals cut out by an arbitrary intermediate point. -/
theorem ae_restrict_Ioc_mem_Ioo_union_Ioo {μ : Measure ℝ} [NullSingletonClass μ] (a b c : ℝ) :
    ∀ᵐ t ∂μ.restrict (Ioc a c), t ∈ Ioo a b ∪ Ioo b c := by
  refine ae_restrict_mem_of_countable_diff measurableSet_Ioc
    ((countable_singleton c).insert b) ?_
  rintro x ⟨hx, hx'⟩
  rcases lt_trichotomy x b with h | h | h
  · exact absurd (Or.inl ⟨hx.1, h⟩) hx'
  · exact Or.inl h
  · exact Or.inr (mem_singleton_iff.2
      (le_antisymm hx.2 (not_lt.1 fun hlt ↦ hx' (Or.inr ⟨h, hlt⟩))))

end MeasureTheory
