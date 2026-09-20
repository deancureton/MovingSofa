import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Portmanteau

noncomputable section

open Filter Set
open scoped BoundedContinuousFunction ENNReal NNReal Topology

namespace MeasureTheory.FiniteMeasure

/-- Weak convergence of finite measures and their restrictions implies weak
convergence of the complementary restrictions. -/
theorem tendsto_restrict_compl_of_tendsto_restrict
    {X ι : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {F : Filter ι} {μs : ι → FiniteMeasure X} {μ : FiniteMeasure X} {s : Set X}
    (hs : MeasurableSet s) (hμ : Tendsto μs F (𝓝 μ))
    (hsμ : Tendsto (fun n ↦ (μs n).restrict s) F (𝓝 (μ.restrict s))) :
    Tendsto (fun n ↦ (μs n).restrict sᶜ) F (𝓝 (μ.restrict sᶜ)) := by
  apply tendsto_iff_forall_integral_tendsto.mpr
  intro f
  have hi (ν : FiniteMeasure X) :
      (∫ x, f x ∂(ν.restrict sᶜ : Measure X)) =
        (∫ x, f x ∂(ν : Measure X)) - (∫ x, f x ∂(ν.restrict s : Measure X)) := by
    have h := integral_add_compl hs (f.integrable (μ := (ν : Measure X)))
    change (∫ x in sᶜ, f x ∂(ν : Measure X)) =
      (∫ x, f x ∂(ν : Measure X)) - (∫ x in s, f x ∂(ν : Measure X))
    linarith
  simpa only [hi] using
    ((tendsto_iff_forall_integral_tendsto.mp hμ) f).sub
      ((tendsto_iff_forall_integral_tendsto.mp hsμ) f)

end MeasureTheory.FiniteMeasure

namespace MeasureTheory.FiniteMeasure

/-- A continuity set has convergent masses under weak convergence of finite measures. -/
theorem tendsto_apply_of_null_frontier
    {X ι : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [HasOuterApproxClosed X] [Nonempty X]
    {F : Filter ι} {μs : ι → FiniteMeasure X} {μ : FiniteMeasure X} {s : Set X}
    (hμ : Tendsto μs F (𝓝 μ)) (hs : μ (frontier s) = 0) :
    Tendsto (fun n ↦ μs n s) F (𝓝 (μ s)) := by
  by_cases hzero : μ = 0
  · subst μ
    have hm := hμ.mass
    simp only [zero_mass] at hm
    have hlim := tendsto_of_tendsto_of_tendsto_of_le_of_le
      (tendsto_const_nhds : Tendsto (fun _ : ι ↦ (0 : ℝ≥0)) F (𝓝 0)) hm
      (fun _ ↦ zero_le) (fun n ↦ (μs n).apply_le_mass s)
    simpa using hlim
  · have hn := μ.tendsto_normalize_of_tendsto hμ hzero
    have hs' : μ.normalize (frontier s) = 0 := by
      rw [μ.normalize_eq_of_nonzero hzero, hs, mul_zero]
    have hset := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto hn hs'
    simpa only [← self_eq_mass_mul_normalize] using hμ.mass.mul hset

end MeasureTheory.FiniteMeasure

namespace MeasureTheory.Measure

/-- Equal atoms on a finite set give equal restrictions to that set. -/
theorem restrict_finset_eq_of_singleton_eq
    {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    {μ ν : Measure X} (s : Finset X) (h : ∀ x ∈ s, μ {x} = ν {x}) :
    μ.restrict (s : Set X) = ν.restrict (s : Set X) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hd : Disjoint ({a} : Set X) (s : Set X) := by simpa using ha
    have heq := ih (fun x hx ↦ h x (Finset.mem_insert_of_mem hx))
    rw [Finset.coe_insert, ← Set.singleton_union]
    rw [restrict_union hd s.measurableSet, restrict_union hd s.measurableSet]
    rw [restrict_singleton, restrict_singleton, h a (Finset.mem_insert_self _ _), heq]

end MeasureTheory.Measure

namespace MeasureTheory.FiniteMeasure

/-- Removing finitely many fixed atoms preserves weak convergence. -/
theorem tendsto_restrict_compl_finset_of_singleton_eq
    {X ι : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [MeasurableSingletonClass X] {F : Filter ι}
    {μs : ι → FiniteMeasure X} {μ : FiniteMeasure X} (s : Finset X)
    (hμ : Tendsto μs F (𝓝 μ))
    (h : ∀ n x, x ∈ s → (μs n : Measure X) {x} = (μ : Measure X) {x}) :
    Tendsto (fun n ↦ (μs n).restrict (s : Set X)ᶜ) F
      (𝓝 (μ.restrict (s : Set X)ᶜ)) := by
  apply tendsto_restrict_compl_of_tendsto_restrict s.measurableSet hμ
  have heq (n : ι) : (μs n).restrict (s : Set X) = μ.restrict (s : Set X) :=
    Subtype.ext (Measure.restrict_finset_eq_of_singleton_eq s (h n))
  simpa only [heq] using
    (tendsto_const_nhds : Tendsto (fun _ : ι ↦ μ.restrict (s : Set X)) F
      (𝓝 (μ.restrict (s : Set X))))

/-- A finite measure weighted by a bounded continuous nonnegative function. -/
private def withDensityNN {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (μ : FiniteMeasure X) (g : X →ᵇ ℝ≥0) : FiniteMeasure X :=
  ⟨(μ : Measure X).withDensity (fun x ↦ g x),
    isFiniteMeasure_withDensity (g.lintegral_lt_top_of_nnreal μ).ne⟩

/-- Weighting by a fixed bounded continuous nonnegative function preserves weak convergence. -/
private theorem tendsto_withDensityNN
    {X ι : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {F : Filter ι} {μs : ι → FiniteMeasure X} {μ : FiniteMeasure X}
    (hμ : Tendsto μs F (𝓝 μ)) (g : X →ᵇ ℝ≥0) :
    Tendsto (fun n ↦ withDensityNN (μs n) g) F (𝓝 (withDensityNN μ g)) := by
  apply tendsto_iff_forall_lintegral_tendsto.mpr
  intro f
  have hprod := (tendsto_iff_forall_lintegral_tendsto.mp hμ) (g * f)
  have h_lintegral (ν : FiniteMeasure X) :
      (∫⁻ x, (f x : ℝ≥0∞) ∂(withDensityNN ν g : Measure X)) =
        ∫⁻ x, ((g * f) x : ℝ≥0∞) ∂(ν : Measure X) := by
    rw [withDensityNN, toMeasure_mk, lintegral_withDensity_eq_lintegral_mul]
    · simp
    · exact (ENNReal.continuous_coe.comp g.continuous).measurable
    · exact (ENNReal.continuous_coe.comp f.continuous).measurable
  simpa only [h_lintegral] using hprod

/-- Weak convergence is preserved by restriction to a measurable continuity set. -/
theorem tendsto_restrict_of_null_frontier
    {X ι : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [HasOuterApproxClosed X] [Nonempty X]
    {F : Filter ι} {μs : ι → FiniteMeasure X} {μ : FiniteMeasure X} {s : Set X}
    (hs : MeasurableSet s) (hμ : Tendsto μs F (𝓝 μ))
    (hfrontier : μ (frontier s) = 0) :
    Tendsto (fun n ↦ (μs n).restrict s) F (𝓝 (μ.restrict s)) := by
  apply tendsto_iff_forall_lintegral_tendsto.mpr
  intro g
  have hweighted := tendsto_withDensityNN hμ g
  have hfrontier' : (withDensityNN μ g) (frontier s) = 0 := by
    apply ENNReal.coe_eq_zero.mp
    rw [ennreal_coeFn_eq_coeFn_toMeasure]
    apply withDensity_absolutelyContinuous (μ : Measure X) (fun x ↦ g x)
    simpa only [← ennreal_coeFn_eq_coeFn_toMeasure, ENNReal.coe_zero] using
      congrArg ((↑) : ℝ≥0 → ℝ≥0∞) hfrontier
  have hmass := tendsto_apply_of_null_frontier hweighted hfrontier'
  have hmass_ennreal := (ENNReal.continuous_coe.tendsto _).comp hmass
  change Tendsto (fun n ↦ (withDensityNN (μs n) g s : ℝ≥0∞)) F
    (𝓝 (withDensityNN μ g s : ℝ≥0∞)) at hmass_ennreal
  have h_lintegral (ν : FiniteMeasure X) :
      (withDensityNN ν g s : ℝ≥0∞) =
        ∫⁻ x in s, (g x : ℝ≥0∞) ∂(ν : Measure X) := by
    rw [ennreal_coeFn_eq_coeFn_toMeasure, withDensityNN, toMeasure_mk, withDensity_apply _ hs]
  simpa only [h_lintegral, restrict_measure_eq] using hmass_ennreal

/-- Fixed atoms on a finite set containing the frontier allow weak restriction convergence. -/
theorem tendsto_restrict_of_frontier_subset_finset
    {X ι : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [HasOuterApproxClosed X] [Nonempty X] [MeasurableSingletonClass X]
    {F : Filter ι} {μs : ι → FiniteMeasure X} {μ : FiniteMeasure X} {s : Set X}
    (hs : MeasurableSet s) (t : Finset X) (hfrontier : frontier s ⊆ (t : Set X))
    (hμ : Tendsto μs F (𝓝 μ))
    (hatoms : ∀ n x, x ∈ t → (μs n : Measure X) {x} = (μ : Measure X) {x}) :
    Tendsto (fun n ↦ (μs n).restrict s) F (𝓝 (μ.restrict s)) := by
  have hremoved := tendsto_restrict_compl_finset_of_singleton_eq t hμ hatoms
  have hzero : (μ.restrict (t : Set X)ᶜ) (frontier s) = 0 := by
    apply (null_iff_toMeasure_null _ _).mpr
    rw [restrict_measure_eq, Measure.restrict_apply measurableSet_frontier]
    have he : frontier s ∩ (t : Set X)ᶜ = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact hx.2 (hfrontier hx.1)
    rw [he, measure_empty]
  have hrestricted := tendsto_restrict_of_null_frontier hs hremoved hzero
  have hfixed (n : ι) : ((μs n).restrict (t : Set X)).restrict s =
      (μ.restrict (t : Set X)).restrict s := by
    congr 1
    exact Subtype.ext (Measure.restrict_finset_eq_of_singleton_eq t (hatoms n))
  have hsplit (ν : FiniteMeasure X) : ν.restrict s =
      (ν.restrict (t : Set X)ᶜ).restrict s + (ν.restrict (t : Set X)).restrict s := by
    apply Subtype.ext
    change (ν : Measure X).restrict s =
      ((ν : Measure X).restrict (t : Set X)ᶜ).restrict s +
        ((ν : Measure X).restrict (t : Set X)).restrict s
    rw [← Measure.restrict_add]
    congr 1
    rw [add_comm, Measure.restrict_add_restrict_compl t.measurableSet]
  have hconst : Tendsto (fun n ↦ ((μs n).restrict (t : Set X)).restrict s) F
      (𝓝 ((μ.restrict (t : Set X)).restrict s)) := by
    simpa only [hfixed] using
      (tendsto_const_nhds : Tendsto (fun _ : ι ↦ (μ.restrict (t : Set X)).restrict s) F _)
  simpa only [← hsplit] using hrestricted.add hconst

end MeasureTheory.FiniteMeasure
