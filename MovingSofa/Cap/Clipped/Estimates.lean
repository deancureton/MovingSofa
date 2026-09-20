import MovingSofa.Motion.RotationAngleCalculation

noncomputable section

namespace MovingSofa

private theorem clippedArea_bound_low {u t : ℝ}
    (ht : 39 / 20 < t) (ht' : t ≤ 11 / 5) (hu : u < 121 / 50) :
    u - (t - 5 / 4) ^ 2 / t < 11 / 5 := by
  have ht0 : 0 < t := by linarith
  have hsq : 49 / 100 < (t - 5 / 4) ^ 2 := by nlinarith
  have hquot : 49 / 220 < (t - 5 / 4) ^ 2 / t := by
    apply (lt_div_iff₀ ht0).2
    nlinarith
  linarith

private theorem clippedArea_bound {C S : ℝ} (hC : 0 < C) (hS : 0 < S)
    (hcircle : S ^ 2 + C ^ 2 = 1) (hC' : C ≤ 5 / 11) :
    let d : ℝ := if S / C < 11 / 5 then 5 / 4 else 11 / 10
    1 / C - (S / C - d) ^ 2 * (C / S) < 11 / 5 := by
  dsimp
  split_ifs with h
  · have ht : 0 < S / C := div_pos hS hC
    have hid : (1 / C) ^ 2 = 1 + (S / C) ^ 2 := by
      field_simp
      nlinarith
    have hu : 11 / 5 ≤ 1 / C := by
      apply (le_div_iff₀ hC).2
      linarith
    have hlo : 39 / 20 < S / C := by nlinarith
    have hhi : 1 / C < 121 / 50 := by
      have hu0 : 0 < 1 / C := by positivity
      nlinarith
    have hb := clippedArea_bound_low hlo h.le hhi
    convert hb using 1
    field_simp
  · have hs1 : S ≤ 1 := by nlinarith [sq_nonneg C]
    have hc : C / (1 + S) ≤ C / S / 2 := by
      have hs' : 0 < 1 + S := by linarith
      apply (div_le_iff₀ hs').2
      field_simp
      nlinarith [mul_nonneg hC.le (sub_nonneg.mpr hs1)]
    have hid : 1 / C - (S / C - 11 / 10) ^ 2 * (C / S) =
        C / (1 + S) + 11 / 5 - (121 / 100) * (C / S) := by
      field_simp
      nlinarith [hcircle]
    rw [hid]
    have hp : 0 < C / S := div_pos hC hS
    linarith

theorem rotationCalculation_area_estimate (ω : RotationCalculationAngle) :
    1 / Real.cos ω.val - (Real.tan ω.val - rotationCalculationMinimum ω) ^ 2 *
      (Real.cos ω.val / Real.sin ω.val) < 11 / 5 := by
  have hw0 : 0 < ω.val :=
    (Real.arccos_pos.mpr (by norm_num : (5 / 11 : ℝ) < 1)).trans_le ω.property.1
  have hC : 0 < Real.cos ω.val :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], ω.property.2⟩
  have hS : 0 < Real.sin ω.val :=
    Real.sin_pos_of_pos_of_lt_pi hw0 (by linarith [ω.property.2, Real.pi_pos])
  have hC' : Real.cos ω.val ≤ 5 / 11 := by
    have h := Real.strictAntiOn_cos.antitoneOn
      (show Real.arccos (5 / 11 : ℝ) ∈ Set.Icc 0 Real.pi from
        ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩)
      (show ω.val ∈ Set.Icc 0 Real.pi from
        ⟨hw0.le, by linarith [ω.property.2, Real.pi_pos]⟩) ω.property.1
    simpa only [Real.cos_arccos (by norm_num : (-1 : ℝ) ≤ 5 / 11)
      (by norm_num : (5 / 11 : ℝ) ≤ 1)] using h
  have hs : (Real.sin ω.val / Real.cos ω.val < 11 / 5) ↔
      ω.val < Real.arctan (11 / 5 : ℝ) := by
    rw [← Real.tan_eq_sin_div_cos, ← Real.arctan_lt_arctan_iff]
    rw [Real.arctan_tan (by linarith [Real.pi_pos]) ω.property.2]
  have hb := clippedArea_bound hC hS (Real.sin_sq_add_cos_sq ω.val) hC'
  dsimp at hb
  simp only [hs] at hb
  simpa only [← Real.tan_eq_sin_div_cos, rotationCalculationMinimum] using hb

theorem rotationCalculationMinimum_pos (ω : RotationCalculationAngle) :
    0 < rotationCalculationMinimum ω := by
  unfold rotationCalculationMinimum
  split_ifs <;> norm_num

theorem rotationCalculationMinimum_lt_tan (ω : RotationCalculationAngle) :
    rotationCalculationMinimum ω < Real.tan ω.val := by
  have hw0 : 0 < ω.val :=
    (Real.arccos_pos.mpr (by norm_num : (5 / 11 : ℝ) < 1)).trans_le ω.property.1
  have hC : 0 < Real.cos ω.val :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], ω.property.2⟩
  have hS : 0 < Real.sin ω.val :=
    Real.sin_pos_of_pos_of_lt_pi hw0 (by linarith [ω.property.2, Real.pi_pos])
  have hC' : Real.cos ω.val ≤ 5 / 11 := by
    have h := Real.cos_le_cos_of_nonneg_of_le_pi (Real.arccos_nonneg (5 / 11))
      (by linarith [ω.property.2, Real.pi_pos] : ω.val ≤ Real.pi) ω.property.1
    simpa only [Real.cos_arccos (by norm_num : (-1 : ℝ) ≤ 5 / 11)
      (by norm_num : (5 / 11 : ℝ) ≤ 1)] using h
  have hsq : Real.cos ω.val ^ 2 ≤ (5 / 11 : ℝ) ^ 2 :=
    pow_le_pow_left₀ hC.le hC' 2
  have ht : (5 / 4 : ℝ) < Real.tan ω.val := by
    rw [Real.tan_eq_sin_div_cos, lt_div_iff₀ hC]
    nlinarith [Real.sin_sq_add_cos_sq ω.val]
  unfold rotationCalculationMinimum
  split_ifs <;> linarith

end MovingSofa
