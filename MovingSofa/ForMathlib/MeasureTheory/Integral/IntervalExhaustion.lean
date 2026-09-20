import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section

open Filter
open scoped Topology

namespace MeasureTheory

/-- Every interior point eventually belongs to the standard inner exhaustion of an interval. -/
theorem eventually_mem_innerIcc_of_mem_Ioo {a b x : ℝ}
    (hx : x ∈ Set.Ioo a b) :
    ∀ᶠ n : ℕ in atTop,
      x ∈ Set.Icc (a + 1 / ((n : ℝ) + 1)) (b - 1 / ((n : ℝ) + 1)) := by
  have hleft := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
    (Iio_mem_nhds (sub_pos.mpr hx.1))
  have hright := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
    (Iio_mem_nhds (sub_pos.mpr hx.2))
  exact (hleft.and hright).mono fun n hn ↦ by
    constructor <;> linarith [hn.1, hn.2]

/-- Each interval in the standard inner exhaustion lies in the open interval. -/
theorem innerIcc_subset_Ioo (a b : ℝ) (n : ℕ) :
    Set.Icc (a + 1 / ((n : ℝ) + 1)) (b - 1 / ((n : ℝ) + 1)) ⊆
      Set.Ioo a b := by
  intro x hx
  have hn : 0 < 1 / ((n : ℝ) + 1) := by positivity
  constructor <;> linarith [hx.1, hx.2]

/-- Integrals over compact intervals exhausting the interior converge to the
integral over the full compact interval. -/
theorem tendsto_integral_innerIcc
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E} {a b : ℝ} (hf : Integrable f (volume.restrict (Set.Icc a b))) :
    Tendsto (fun n : ℕ ↦ ∫ x in Set.Icc (a + 1 / ((n : ℝ) + 1))
        (b - 1 / ((n : ℝ) + 1)), f x)
      atTop (nhds (∫ x in Set.Icc a b, f x)) := by
  let t := Set.Icc a b
  let s : ℕ → Set ℝ := fun n ↦
    Set.Icc (a + 1 / ((n : ℝ) + 1)) (b - 1 / ((n : ℝ) + 1))
  have hs (n : ℕ) : MeasurableSet (s n) := measurableSet_Icc
  have hft : Integrable (t.indicator f) volume :=
    IntegrableOn.integrable_indicator hf measurableSet_Icc
  have hmeas (n : ℕ) : AEStronglyMeasurable ((s n).indicator f) volume := by
    apply (hft.1.indicator (hs n)).congr
    filter_upwards [] with x
    by_cases hx : x ∈ s n
    · have hxi := innerIcc_subset_Ioo a b n hx
      have hxt : x ∈ t := ⟨hxi.1.le, hxi.2.le⟩
      simp [Set.indicator, hx, hxt]
    · simp [Set.indicator, hx]
  have hbound (n : ℕ) : ∀ᵐ x ∂volume,
      ‖(s n).indicator f x‖ ≤ ‖t.indicator f x‖ :=
    Filter.Eventually.of_forall fun x ↦ by
      by_cases hx : x ∈ s n
      · have hxi := innerIcc_subset_Ioo a b n hx
        have hxt : x ∈ t := ⟨hxi.1.le, hxi.2.le⟩
        simp [Set.indicator, hx, hxt]
      · simp only [Set.indicator, hx, ↓reduceIte, norm_zero]
        exact norm_nonneg _
  have hIooVolume : Set.Ioo a b =ᵐ[volume] Set.Icc a b := Ioo_ae_eq_Icc
  have hlim : ∀ᵐ x ∂volume, Tendsto (fun n ↦ (s n).indicator f x)
      atTop (nhds (t.indicator f x)) := by
    filter_upwards [hIooVolume] with x hxeq
    by_cases hx : x ∈ Set.Ioo a b
    · have hev := eventually_mem_innerIcc_of_mem_Ioo hx
      apply tendsto_const_nhds.congr'
      exact hev.mono fun n hn ↦
        (Set.indicator_of_mem (hxeq.mp hx) f).trans
          (Set.indicator_of_mem hn f).symm
    · have hxt : x ∉ t := fun h ↦ hx (hxeq.mpr h)
      apply tendsto_const_nhds.congr'
      filter_upwards [] with n
      have hxn : x ∉ s n := fun h ↦ by
        have hxi := innerIcc_subset_Ioo a b n h
        exact hxt ⟨hxi.1.le, hxi.2.le⟩
      simp only [Set.indicator, hxn, hxt, ↓reduceIte]
  have ht := tendsto_integral_of_dominated_convergence (μ := volume)
    (fun x ↦ ‖t.indicator f x‖) hmeas hft.norm hbound hlim
  simpa only [s, t, integral_indicator, hs, measurableSet_Icc] using ht

end MeasureTheory
