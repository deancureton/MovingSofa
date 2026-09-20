import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Tactic.Linarith

namespace Real.Angle

/-- Distinct reals at distance less than a full turn have distinct angles. -/
theorem coe_ne_coe_of_abs_sub_lt {x y : ℝ} (hne : x ≠ y) (h : |x - y| < 2 * Real.pi) :
    ((x : ℝ) : Real.Angle) ≠ ((y : ℝ) : Real.Angle) := by
  intro he
  rw [Real.Angle.angle_eq_iff_two_pi_dvd_sub] at he
  obtain ⟨k, hk⟩ := he
  have hpi := Real.pi_pos
  rw [abs_lt] at h
  rcases lt_trichotomy k 0 with hk0 | rfl | hk0
  · have hk' : (k : ℝ) ≤ -1 := by exact_mod_cast (by omega : k ≤ -1)
    nlinarith [h.1]
  · simp only [Int.cast_zero, mul_zero] at hk
    exact hne (by linarith)
  · have hk' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : (1 : ℤ) ≤ k)
    nlinarith [h.2]

end Real.Angle
