import Mathlib.Analysis.Calculus.ContDiff.Deriv

open Set

/-- Glue one-sided derivatives on a closed interval, including its endpoints. -/
theorem hasDerivWithinAt_Icc_of_oneSided {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {a b t : ℝ} (hab : a < b)
    (ht : t ∈ Icc a b) {f : ℝ → E} {d : E}
    (hr : t < b → HasDerivWithinAt f d (Ici t) t)
    (hl : a < t → HasDerivWithinAt f d (Iic t) t) :
    HasDerivWithinAt f d (Icc a b) t := by
  rcases eq_or_lt_of_le ht.1 with rfl | hat
  · exact (hr hab).mono Icc_subset_Ici_self
  · rcases lt_or_eq_of_le ht.2 with htb | rfl
    · have h := (hl hat).union (hr htb)
      rw [Iic_union_Ici] at h
      exact h.mono (subset_univ _)
    · exact (hl hat).mono Icc_subset_Iic_self

/-- A continuous derivative field on a uniquely differentiable set gives order-one regularity. -/
theorem contDiffOn_one_of_continuous_derivative {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set ℝ}
    (hs : UniqueDiffOn ℝ s) (f : ℝ → E) (d : s → E) (hd : Continuous d)
    (hf : ∀ t : s, HasDerivWithinAt f (d t) s t) : ContDiffOn ℝ 1 f s := by
  apply (contDiffOn_one_iff_derivWithin hs).mpr
  refine ⟨fun t ht ↦ (hf ⟨t, ht⟩).differentiableWithinAt, ?_⟩
  apply continuousOn_iff_continuous_domRestrict.mpr
  apply hd.congr
  intro t
  exact ((hf t).derivWithin (hs t t.property)).symm

/-- Glue two everywhere differentiable functions along the switch `{s ≤ c}`.  If the values
and the derivatives agree at `c`, the glued function is differentiable everywhere and its
derivative is the analogous glue of the two derivative fields.  At `c` itself the statement
is genuine two-sided differentiability, obtained from the two one-sided derivatives. -/
theorem hasDerivAt_if_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g f' g' : ℝ → E} {c : ℝ}
    (hf : ∀ t, HasDerivAt f (f' t) t) (hg : ∀ t, HasDerivAt g (g' t) t)
    (hfg : f c = g c) (hfg' : f' c = g' c) (t : ℝ) :
    HasDerivAt (fun s => if s ≤ c then f s else g s) (if t ≤ c then f' t else g' t) t := by
  rcases lt_trichotomy t c with ht | ht | ht
  · rw [ite_eq_left ht.le]
    refine (hf t).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds ht] with s hs
    exact ite_eq_left (le_of_lt hs)
  · subst ht
    rw [ite_eq_left le_rfl]
    have hl : HasDerivWithinAt (fun s => if s ≤ t then f s else g s) (f' t) (Iic t) t :=
      (hf t).hasDerivWithinAt.congr (fun _ hs => ite_eq_left hs) (ite_eq_left le_rfl)
    have hr : HasDerivWithinAt (fun s => if s ≤ t then f s else g s) (f' t) (Ici t) t := by
      rw [hfg']
      refine (hg t).hasDerivWithinAt.congr (fun s hs => ?_) (by rw [ite_eq_left le_rfl, hfg])
      rcases eq_or_lt_of_le (mem_Ici.mp hs) with rfl | hlt
      · rw [ite_eq_left le_rfl, hfg]
      · rw [ite_eq_right (not_le.mpr hlt)]
    have hu := hl.union hr
    rw [Iic_union_Ici] at hu
    exact hasDerivWithinAt_univ.mp hu
  · rw [ite_eq_right (not_le.mpr ht)]
    refine (hg t).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact ite_eq_right (not_le.mpr hs)

/-- A globally defined continuous derivative field witnesses continuous differentiability. -/
theorem contDiff_one_of_hasDerivAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f f' : ℝ → E} (hf : ∀ t, HasDerivAt f (f' t) t) (hf' : Continuous f') :
    ContDiff ℝ 1 f :=
  contDiff_one_iff_deriv.2 ⟨fun t => (hf t).differentiableAt, deriv_eq hf ▸ hf'⟩
