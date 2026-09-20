import MovingSofa.Motion.Translation
import MovingSofa.Motion.CommonSubset
import MovingSofa.Geometry.Support

noncomputable section

namespace MovingSofa

theorem exists_standardPosition_translation (s : Set Point) (ω : ℝ)
    (hs : HasRotationAngle s ω) (hω : ω ∈ Set.Ioc 0 (Real.pi / 2)) :
    (∃ v : Point, IsStandardPosition ((fun p ↦ p + v) '' s) ω) ∧
    (∀ v w : Point,
      IsStandardPosition ((fun p ↦ p + v) '' s) ω →
      IsStandardPosition ((fun p ↦ p + w) '' s) ω →
      (ω < Real.pi / 2 → v = w) ∧ (ω = Real.pi / 2 → v 1 = w 1)) ∧
    (∀ v : Point, IsStandardPosition ((fun p ↦ p + v) '' s) ω →
      ω = Real.pi / 2 → ∀ a : ℝ,
        IsStandardPosition ((fun p ↦ p + (v + a • normalVector 0)) '' s) ω) ∧
    (∀ v : Point, IsStandardPosition ((fun p ↦ p + v) '' s) ω →
      (fun p ↦ p + v) '' s ⊆ (stripParallelogram ω).1) := by
  have hc : IsCompact s := hs.isCompact hω
  have hne : s.Nonempty := by
    obtain ⟨_, hm, _⟩ := hs
    exact hm.1.nonempty
  have hadd (v : Point) (t : Real.Angle) :
      supportValue ((fun p ↦ p + v) '' s) t =
        supportValue s t + inner ℝ v (normalVector t) :=
    supportValue_image_add_of_isCompact hc hne v t
  have hcos (hlt : ω < Real.pi / 2) : Real.cos ω ≠ 0 :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [hω.1, Real.pi_pos], hlt⟩).ne'
  constructor
  · rcases lt_or_eq_of_le hω.2 with hlt | rfl
    · let v : Point := !₂[
          (1 - supportValue s (ω : Real.Angle) -
            (1 - supportValue s ((Real.pi / 2 : ℝ) : Real.Angle)) * Real.sin ω) /
              Real.cos ω,
          1 - supportValue s ((Real.pi / 2 : ℝ) : Real.Angle)]
      refine ⟨v, hc.image (by fun_prop), hasRotationAngle_image_add s v ω hs,
        hω.1, hω.2, ?_, ?_⟩
      · rw [hadd]
        simp only [v, normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two, Real.inner_apply,
          Real.Angle.cos_coe, Real.Angle.sin_coe, Matrix.cons_val_zero,
          Matrix.cons_val_one]
        field_simp [hcos hlt]
        ring
      · rw [hadd]
        simp [v, normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two]
    · let v : Point := !₂[0,
          1 - supportValue s ((Real.pi / 2 : ℝ) : Real.Angle)]
      refine ⟨v, hc.image (by fun_prop),
        hasRotationAngle_image_add s v (Real.pi / 2) hs, hω.1, hω.2, ?_, ?_⟩
      · rw [hadd]
        simp [v, normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two]
      · rw [hadd]
        simp [v, normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two]
  · constructor
    · intro v w hv hw
      have hvω := hv.2.2.2.2.1
      have hvπ := hv.2.2.2.2.2
      have hwω := hw.2.2.2.2.1
      have hwπ := hw.2.2.2.2.2
      rw [hadd] at hvω hvπ hwω hwπ
      constructor
      · intro hlt
        have hy : v 1 = w 1 := by
          simp [normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two] at hvπ hwπ
          linarith
        apply PiLp.ext
        intro i
        fin_cases i
        · have hcω := hcos hlt
          change v 0 = w 0
          simp [normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two] at hvω hwω
          rw [hy] at hvω
          apply mul_left_cancel₀ hcω
          linarith [hvω, hwω]
        · exact hy
      · intro _
        simp [normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two] at hvπ hwπ
        linarith
    · constructor
      · intro v hv hωeq a
        subst ω
        have hvπ := hv.2.2.2.2.2
        rw [hadd] at hvπ
        refine ⟨hc.image (by fun_prop),
          hasRotationAngle_image_add s (v + a • normalVector 0) (Real.pi / 2) hs,
          hω.1, hω.2, ?_, ?_⟩
        · rw [hadd]
          simp [normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two] at hvπ ⊢
          linarith
        · rw [hadd]
          simp [normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two] at hvπ ⊢
          linarith
      · intro v hv
        exact hv.subset_strips

end MovingSofa
