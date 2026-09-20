import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue

/-!
# First return to a level

A continuous real function that starts strictly below a level and reaches it has a smallest
time at which it attains that level, and its derivative there is nonnegative.
-/

/-- A continuous function below a level at the left end has a first return to that level. -/
theorem exists_first_return {g : ℝ → ℝ} {a b c : ℝ} (hab : a < b)
    (hcont : ContinuousOn g (Set.Icc a b)) (hga : g a < c) (hgb : c ≤ g b) :
    ∃ t ∈ Set.Ioc a b, g t = c ∧ ∀ u ∈ Set.Ico a t, g u < c := by
  set E : Set ℝ := Set.Icc a b ∩ g ⁻¹' Set.Ici c with hE
  have hEcl : IsClosed E := hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hEne : E.Nonempty := ⟨b, ⟨hab.le, le_refl b⟩, hgb⟩
  have hEbdd : BddBelow E := ⟨a, fun u hu => hu.1.1⟩
  set t : ℝ := sInf E with ht
  have htE : t ∈ E := hEcl.csInf_mem hEne hEbdd
  have htlb : ∀ u ∈ E, t ≤ u := fun u hu => csInf_le hEbdd hu
  have hta : a < t := by
    rcases eq_or_lt_of_le htE.1.1 with h | h
    · exact absurd htE.2 (by rw [← h]; exact not_le.mpr hga)
    · exact h
  have hleft : ∀ u ∈ Set.Ico a t, g u < c := by
    intro u hu
    by_contra hcc
    push Not at hcc
    exact absurd (htlb u ⟨⟨hu.1, le_trans hu.2.le htE.1.2⟩, hcc⟩) (not_le.mpr hu.2)
  have hIco : Set.Ico a t ∈ nhdsWithin t (Set.Iio t) := Ico_mem_nhdsLT hta
  have hsub : Set.Ico a t ⊆ Set.Icc a b := fun u hu => ⟨hu.1, le_trans hu.2.le htE.1.2⟩
  have htend : Filter.Tendsto g (nhdsWithin t (Set.Iio t)) (nhds (g t)) :=
    ((hcont t htE.1).mono hsub).tendsto.mono_left (nhdsWithin_le_of_mem hIco)
  refine ⟨t, ⟨hta, htE.1.2⟩, le_antisymm ?_ htE.2, hleft⟩
  exact le_of_tendsto htend (Filter.eventually_of_mem hIco fun u hu => (hleft u hu).le)

/-- At a first return from below, the derivative is nonnegative. -/
theorem nonneg_of_first_return {g : ℝ → ℝ} {a t c d : ℝ} (hat : a < t)
    (hd : HasDerivAt g d t) (hgt : g t = c) (hleft : ∀ u ∈ Set.Ico a t, g u < c) :
    0 ≤ d := by
  have hIco : Set.Ico a t ∈ nhdsWithin t (Set.Iio t) := Ico_mem_nhdsLT hat
  have hsl := (hasDerivAt_iff_tendsto_slope.mp hd).mono_left
    (nhdsWithin_mono t (fun x hx => ne_of_lt hx) :
      nhdsWithin t (Set.Iio t) ≤ nhdsWithin t {t}ᶜ)
  refine ge_of_tendsto hsl (Filter.eventually_of_mem hIco fun u hu => ?_)
  rw [slope_def_field, hgt]
  exact le_of_lt (div_pos_of_neg_of_neg (by linarith only [hleft u hu])
    (by linarith only [hu.2]))
