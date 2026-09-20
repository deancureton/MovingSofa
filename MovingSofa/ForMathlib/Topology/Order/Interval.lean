import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas

namespace Set

instance instCompactIccSpaceIcc (a b : ℝ) : CompactIccSpace (Icc a b) :=
  ⟨fun {_ _} ↦ isClosed_Icc.isCompact⟩

end Set

/-- Reverse a closed real interval about its midpoint. -/
def Set.Icc.reverse {a b : ℝ} (_hab : a ≤ b) :
    Set.Icc a b → Set.Icc a b := fun t ↦
  ⟨a + b - t, by linarith [t.property.2], by linarith [t.property.1]⟩

/-- Interval reversal is continuous. -/
theorem Set.Icc.continuous_reverse {a b : ℝ} (hab : a ≤ b) :
    Continuous (Set.Icc.reverse hab) :=
  (continuous_const.add continuous_const |>.sub continuous_subtype_val).subtype_mk _

/-- Interval reversal is antitone. -/
theorem Set.Icc.antitone_reverse {a b : ℝ} (hab : a ≤ b) :
    Antitone (Set.Icc.reverse hab) := by
  intro x y hxy
  have hxy' : (x : ℝ) ≤ y := hxy
  change a + b - (y : ℝ) ≤ a + b - (x : ℝ)
  linarith

/-- Reversing a closed interval twice is the identity. -/
theorem Set.Icc.involutive_reverse {a b : ℝ} (hab : a ≤ b) :
    Function.Involutive (Set.Icc.reverse hab) := by
  intro x
  apply Subtype.ext
  simp [Set.Icc.reverse]

/-- Interval reversal is surjective. -/
theorem Set.Icc.surjective_reverse {a b : ℝ} (hab : a ≤ b) :
    Function.Surjective (Set.Icc.reverse hab) :=
  (Set.Icc.involutive_reverse hab).surjective

open Set Filter
open scoped Topology

/-- Replace the terminal value of a one-sided continuous function by its left limit. -/
theorem continuousOn_replace_right_endpoint {E : Type*} [TopologicalSpace E]
    {a b : ℝ} (hab : a < b) (f : ℝ → E) (z : E)
    (hr : ∀ t ∈ Ico a b, Tendsto f (𝓝[>] t) (𝓝 (f t)))
    (hl : ∀ t ∈ Ioo a b, Tendsto f (𝓝[<] t) (𝓝 (f t)))
    (hb : Tendsto f (𝓝[<] b) (𝓝 z)) :
    ContinuousOn (fun t ↦ if t = b then z else f t) (Icc a b) := by
  let g : ℝ → E := fun t ↦ if t = b then z else f t
  have heql {t : ℝ} (ht : t ≤ b) : g =ᶠ[𝓝[<] t] f := by
    filter_upwards [self_mem_nhdsWithin] with u hu
    have hne : u ≠ b := (lt_of_lt_of_le hu ht).ne
    simp [g, hne]
  have heqr {t : ℝ} (ht : t < b) : g =ᶠ[𝓝[>] t] f := by
    filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds ht)] with u hu
    simp [g, (show u ≠ b from hu.ne)]
  intro t ht
  change ContinuousWithinAt g (Icc a b) t
  rcases eq_or_lt_of_le ht.1 with rfl | hat
  · have h : ContinuousWithinAt g (Ioi a) a := by
      change Tendsto g _ _
      simpa only [g, ite_eq_right hab.ne] using (hr a ⟨le_rfl, hab⟩).congr' (heqr hab).symm
    exact (continuousWithinAt_Ioi_iff_Ici.mp h).mono Icc_subset_Ici_self
  · rcases lt_or_eq_of_le ht.2 with htb | rfl
    · apply ContinuousAt.continuousWithinAt
      apply continuousAt_iff_continuous_left'_right'.mpr
      constructor
      · change Tendsto g _ _
        simpa only [g, ite_eq_right htb.ne] using (hl t ⟨hat, htb⟩).congr' (heql htb.le).symm
      · change Tendsto g _ _
        simpa only [g, ite_eq_right htb.ne] using (hr t ⟨hat.le, htb⟩).congr' (heqr htb).symm
    · have h : ContinuousWithinAt g (Iio t) t := by
        change Tendsto g _ _
        simpa only [g, ite_eq_left rfl] using hb.congr' (heql le_rfl).symm
      exact (continuousWithinAt_Iio_iff_Iic.mp h).mono Icc_subset_Iic_self

/-- Every compact real interval carries finite monotone partitions, with prescribed
endpoints, whose mesh eventually falls below any positive threshold. -/
theorem Set.Icc.exists_partitions_mesh_tendsto_zero {a b : ℝ} (hab : a ≤ b) :
    ∃ cuts : ∀ k : ℕ, Fin (k + 2) → Set.Icc a b,
      (∀ k, Monotone (cuts k)) ∧ (∀ k, (cuts k 0 : ℝ) = a) ∧
      (∀ k, (cuts k (Fin.last (k + 1)) : ℝ) = b) ∧
      ∀ δ > 0, ∀ᶠ k in Filter.atTop, ∀ i : Fin (k + 1),
        (cuts k i.succ : ℝ) - (cuts k i.castSucc : ℝ) < δ := by
  let cuts (k : ℕ) (i : Fin (k + 2)) : Set.Icc a b :=
    ⟨a + (b - a) * (i : ℝ) / (k + 1), by
      have hk : (0 : ℝ) < k + 1 := by positivity
      have hi : (i : ℝ) ≤ k + 1 := by exact_mod_cast Nat.le_of_lt_succ i.isLt
      constructor
      · exact le_add_of_nonneg_right (div_nonneg
          (mul_nonneg (sub_nonneg.mpr hab) (Nat.cast_nonneg _)) hk.le)
      · have hmul := mul_le_mul_of_nonneg_left hi (sub_nonneg.mpr hab)
        have hdiv : (b - a) * (i : ℝ) / (k + 1) ≤ b - a :=
          (div_le_iff₀ hk).mpr hmul
        linarith⟩
  refine ⟨cuts, ?_, ?_, ?_, ?_⟩
  · intro k i j hij
    change a + (b - a) * (i : ℝ) / (k + 1) ≤ a + (b - a) * (j : ℝ) / (k + 1)
    gcongr
    exact_mod_cast hij
  · intro k
    simp [cuts]
  · intro k
    dsimp [cuts]
    push_cast
    rw [mul_div_cancel_right₀ _ (by positivity)]
    ring
  · intro δ hδ
    have ht : Filter.Tendsto (fun k : ℕ ↦ (b - a) / (k + 1))
        Filter.atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop (Filter.tendsto_atTop_add_const_right _ 1
        tendsto_natCast_atTop_atTop)
    filter_upwards [ht.eventually (gt_mem_nhds hδ)] with k hk
    intro i
    convert hk using 1
    dsimp [cuts]
    push_cast
    ring

/-- The increasing affine surjection between two nondegenerate closed intervals. -/
theorem Set.Icc.exists_affine_monotone_surjection {a b c d : ℝ} (hab : a < b) (hcd : c < d) :
    ∃ φ : Set.Icc a b → Set.Icc c d, Continuous φ ∧ Monotone φ ∧ Function.Surjective φ ∧
      ∀ t : Set.Icc a b, (φ t : ℝ) = c + ((t : ℝ) - a) / (b - a) * (d - c) := by
  have hba : (0 : ℝ) < b - a := by linarith
  have hdc : (0 : ℝ) < d - c := by linarith
  have hfrac : ∀ t : Set.Icc a b,
      0 ≤ ((t : ℝ) - a) / (b - a) ∧ ((t : ℝ) - a) / (b - a) ≤ 1 := by
    intro t
    refine ⟨div_nonneg (by linarith [t.property.1]) hba.le, ?_⟩
    rw [div_le_one hba]
    linarith [t.property.2]
  refine ⟨fun t ↦ ⟨c + ((t : ℝ) - a) / (b - a) * (d - c), ?_, ?_⟩, ?_, ?_, ?_, fun _ ↦ rfl⟩
  · nlinarith [(hfrac t).1]
  · nlinarith [(hfrac t).2]
  · exact Continuous.subtype_mk (by fun_prop) _
  · intro s t hst
    have hst' : (s : ℝ) ≤ (t : ℝ) := hst
    have hdiv : ((s : ℝ) - a) / (b - a) ≤ ((t : ℝ) - a) / (b - a) := by gcongr
    show c + ((s : ℝ) - a) / (b - a) * (d - c) ≤ c + ((t : ℝ) - a) / (b - a) * (d - c)
    nlinarith
  · intro y
    have hyl : 0 ≤ ((y : ℝ) - c) / (d - c) := div_nonneg (by linarith [y.property.1]) hdc.le
    have hyr : ((y : ℝ) - c) / (d - c) ≤ 1 := by
      rw [div_le_one hdc]
      linarith [y.property.2]
    refine ⟨⟨a + ((y : ℝ) - c) / (d - c) * (b - a), by nlinarith, by nlinarith⟩, ?_⟩
    apply Subtype.ext
    show c + (a + ((y : ℝ) - c) / (d - c) * (b - a) - a) / (b - a) * (d - c) = (y : ℝ)
    field_simp
    ring

/-- The decreasing affine surjection between two nondegenerate closed intervals: the increasing
one reflected in the midpoint of its codomain. -/
theorem Set.Icc.exists_affine_antitone_surjection {a b c d : ℝ} (hab : a < b) (hcd : c < d) :
    ∃ φ : Set.Icc a b → Set.Icc c d, Continuous φ ∧ Antitone φ ∧ Function.Surjective φ ∧
      ∀ t : Set.Icc a b, (φ t : ℝ) = d - ((t : ℝ) - a) / (b - a) * (d - c) := by
  obtain ⟨φ, hφc, hφm, hφs, hφv⟩ := Set.Icc.exists_affine_monotone_surjection hab hcd
  refine ⟨fun t ↦ ⟨c + d - (φ t : ℝ), ?_, ?_⟩, ?_, ?_, ?_, fun t ↦ ?_⟩
  · linarith [(φ t).property.2]
  · linarith [(φ t).property.1]
  · exact (continuous_const.sub (continuous_subtype_val.comp hφc)).subtype_mk _
  · intro s t hst
    exact Subtype.mk_le_mk.mpr (by linarith [show (φ s : ℝ) ≤ (φ t : ℝ) from hφm hst])
  · intro y
    have hy : c + d - (y : ℝ) ∈ Set.Icc c d :=
      ⟨by linarith [y.property.2], by linarith [y.property.1]⟩
    obtain ⟨t, ht⟩ := hφs ⟨c + d - (y : ℝ), hy⟩
    refine ⟨t, Subtype.ext ?_⟩
    show c + d - (φ t : ℝ) = (y : ℝ)
    rw [show (φ t : ℝ) = c + d - (y : ℝ) from congrArg Subtype.val ht]
    ring
  · show c + d - (φ t : ℝ) = _
    rw [hφv t]
    ring

/-- The translation of the unit interval onto a closed interval of length one. -/
theorem Set.Icc.exists_translation_surjection {c d : ℝ} (hcd : d = c + 1) :
    ∃ φ : Set.Icc (0 : ℝ) 1 → Set.Icc c d, Continuous φ ∧ Monotone φ ∧
      Function.Surjective φ ∧ ∀ u : Set.Icc (0 : ℝ) 1, (φ u : ℝ) = c + (u : ℝ) := by
  obtain ⟨φ, hφc, hφm, hφs, hφv⟩ :=
    Set.Icc.exists_affine_monotone_surjection zero_lt_one (show c < d by rw [hcd]; linarith)
  exact ⟨φ, hφc, hφm, hφs, fun u ↦ by rw [hφv u, hcd]; ring⟩
