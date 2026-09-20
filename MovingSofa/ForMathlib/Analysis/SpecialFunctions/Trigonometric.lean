import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import MovingSofa.ForMathlib.Analysis.SpecificLimits.AlternatingBracket
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-- The tangent of half a complementary angle is secant minus tangent on the first quadrant. -/
theorem Real.tan_pi_div_two_sub_div_two (ω : ℝ) (hω : ω ∈ Set.Ico 0 (Real.pi / 2)) :
    Real.tan ((Real.pi / 2 - ω) / 2) = (Real.cos ω)⁻¹ - Real.tan ω := by
  let u := (Real.pi / 2 - ω) / 2
  have hu : 0 < Real.cos u := Real.cos_pos_of_mem_Ioo ⟨by
    dsimp [u]
    linarith [Real.pi_pos, hω.1, hω.2], by
    dsimp [u]
    linarith [Real.pi_pos, hω.1, hω.2]⟩
  have hw : 0 < Real.cos ω :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hω.1, hω.2], hω.2⟩
  have h2 : 2 * u = Real.pi / 2 - ω := by
    dsimp [u]
    ring
  have hs : 2 * Real.sin u * Real.cos u = Real.cos ω := by
    rw [← Real.sin_two_mul, h2, Real.sin_pi_div_two_sub]
  have hc : 2 * Real.cos u ^ 2 - 1 = Real.sin ω := by
    rw [← Real.cos_two_mul, h2, Real.cos_pi_div_two_sub]
  change Real.tan u = _
  rw [Real.tan_eq_sin_div_cos, Real.tan_eq_sin_div_cos]
  field_simp [hu.ne', hw.ne']
  nlinarith [Real.sin_sq_add_cos_sq u]

/-- Cotangent is antitone between its consecutive poles at negative pi and zero. -/
theorem Real.antitoneOn_cos_div_sin_Ioo_neg_pi_zero :
    AntitoneOn (fun x : ℝ ↦ Real.cos x / Real.sin x) (Set.Ioo (-Real.pi) 0) := by
  intro x hx y hy hxy
  have hxsin := Real.sin_neg_of_neg_of_neg_pi_lt hx.2 hx.1
  have hysin := Real.sin_neg_of_neg_of_neg_pi_lt hy.2 hy.1
  change Real.cos y / Real.sin y ≤ Real.cos x / Real.sin x
  rw [← neg_div_neg_eq (Real.cos y) (Real.sin y),
    ← neg_div_neg_eq (Real.cos x) (Real.sin x)]
  apply (div_le_div_iff₀ (neg_pos.mpr hysin) (neg_pos.mpr hxsin)).mpr
  have hsin : 0 ≤ Real.sin (y - x) := Real.sin_nonneg_of_nonneg_of_le_pi
    (by linarith) (by linarith [hx.1, hy.2])
  rw [Real.sin_sub] at hsin
  nlinarith

/-- A cubic upper bound for the tangent on `[0, 1]`, companion to `Real.sin_gt_sub_cube`. -/
theorem Real.tan_le_self_add_cube {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.tan x ≤ x + 4 / 3 * x ^ 3 := by
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hcos : 0 < Real.cos x :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hcl : 1 - x ^ 2 / 2 ≤ Real.cos x := Real.one_sub_sq_div_two_le_cos
  have hs : Real.sin x ≤ x := Real.sin_le hx
  rw [Real.tan_eq_sin_div_cos, div_le_iff₀ hcos]
  have h1 : (0 : ℝ) ≤ x + 4 / 3 * x ^ 3 := by positivity
  have h2 : (x + 4 / 3 * x ^ 3) * (1 - x ^ 2 / 2) ≤ (x + 4 / 3 * x ^ 3) * Real.cos x :=
    mul_le_mul_of_nonneg_left hcl h1
  have h3 : x ≤ (x + 4 / 3 * x ^ 3) * (1 - x ^ 2 / 2) := by
    nlinarith [mul_nonneg (pow_nonneg hx 3) (show (0 : ℝ) ≤ 5 / 6 - 2 / 3 * x ^ 2 by nlinarith)]
  linarith

/-- Leibniz bracketing of the sine by its Maclaurin partial sums: for `0 ≤ x` with
`x ^ 2 ≤ (4 * N + 2) * (4 * N + 3)` the value `Real.sin x` lies between the partial sums of
`2 * N` and of `2 * N + 1` terms, the first of which undershoots and the second overshoots. -/
theorem Real.sin_mem_Icc_taylor_sums (N : ℕ) {x : ℝ} (hx0 : 0 ≤ x)
    (hx : x ^ 2 ≤ ((4 * N + 2) * (4 * N + 3) : ℕ)) :
    Real.sin x ∈ Set.Icc
      (∑ k ∈ Finset.range (2 * N),
        (-1 : ℝ) ^ k * x ^ (2 * k + 1) / (Nat.factorial (2 * k + 1) : ℝ))
      (∑ k ∈ Finset.range (2 * N + 1),
        (-1 : ℝ) ^ k * x ^ (2 * k + 1) / (Nat.factorial (2 * k + 1) : ℝ)) := by
  have hsum : ∀ n : ℕ, (∑ i ∈ Finset.range n,
        (-1 : ℝ) ^ i * (x ^ (2 * i + 1) / (Nat.factorial (2 * i + 1) : ℝ)))
      = ∑ k ∈ Finset.range n,
        (-1 : ℝ) ^ k * x ^ (2 * k + 1) / (Nat.factorial (2 * k + 1) : ℝ) :=
    fun n ↦ Finset.sum_congr rfl fun k _ ↦ (mul_div_assoc _ _ _).symm
  have htend : Filter.Tendsto (fun n ↦ ∑ i ∈ Finset.range n,
      (-1 : ℝ) ^ i * (x ^ (2 * i + 1) / (Nat.factorial (2 * i + 1) : ℝ)))
      Filter.atTop (nhds (Real.sin x)) := by
    have h := (Real.hasSum_sin x).tendsto_sum_nat
    simpa only [mul_div_assoc] using h
  have hfa : Antitone fun n : ℕ ↦
      x ^ (2 * (2 * N + n) + 1) / (Nat.factorial (2 * (2 * N + n) + 1) : ℝ) := by
    have e : ∀ n : ℕ, 2 * (2 * N + n) + 1 = 2 * n + (4 * N + 1) := fun n ↦ by omega
    simp only [e]
    refine antitone_pow_div_factorial_two_mul_add (a := 4 * N + 1) hx0 ?_
    refine hx.trans (le_of_eq ?_)
    push_cast
    ring
  obtain ⟨hlow, hhigh⟩ :=
    alternating_series_bracket_of_antitone_shift
      (f := fun k : ℕ ↦ x ^ (2 * k + 1) / (Nat.factorial (2 * k + 1) : ℝ)) N htend hfa
  rw [hsum] at hlow hhigh
  exact ⟨hlow, hhigh⟩

/-- Leibniz bracketing of the cosine by its Maclaurin partial sums: for `0 ≤ x` with
`x ^ 2 ≤ (4 * N + 1) * (4 * N + 2)` the value `Real.cos x` lies between the partial sums of
`2 * N` and of `2 * N + 1` terms, the first of which undershoots and the second overshoots. -/
theorem Real.cos_mem_Icc_taylor_sums (N : ℕ) {x : ℝ} (hx0 : 0 ≤ x)
    (hx : x ^ 2 ≤ ((4 * N + 1) * (4 * N + 2) : ℕ)) :
    Real.cos x ∈ Set.Icc
      (∑ k ∈ Finset.range (2 * N),
        (-1 : ℝ) ^ k * x ^ (2 * k) / (Nat.factorial (2 * k) : ℝ))
      (∑ k ∈ Finset.range (2 * N + 1),
        (-1 : ℝ) ^ k * x ^ (2 * k) / (Nat.factorial (2 * k) : ℝ)) := by
  have hsum : ∀ n : ℕ, (∑ i ∈ Finset.range n,
        (-1 : ℝ) ^ i * (x ^ (2 * i) / (Nat.factorial (2 * i) : ℝ)))
      = ∑ k ∈ Finset.range n,
        (-1 : ℝ) ^ k * x ^ (2 * k) / (Nat.factorial (2 * k) : ℝ) :=
    fun n ↦ Finset.sum_congr rfl fun k _ ↦ (mul_div_assoc _ _ _).symm
  have htend : Filter.Tendsto (fun n ↦ ∑ i ∈ Finset.range n,
      (-1 : ℝ) ^ i * (x ^ (2 * i) / (Nat.factorial (2 * i) : ℝ)))
      Filter.atTop (nhds (Real.cos x)) := by
    have h := (Real.hasSum_cos x).tendsto_sum_nat
    simpa only [mul_div_assoc] using h
  have hfa : Antitone fun n : ℕ ↦
      x ^ (2 * (2 * N + n)) / (Nat.factorial (2 * (2 * N + n)) : ℝ) := by
    have e : ∀ n : ℕ, 2 * (2 * N + n) = 2 * n + 4 * N := fun n ↦ by omega
    simp only [e]
    refine antitone_pow_div_factorial_two_mul_add (a := 4 * N) hx0 ?_
    refine hx.trans (le_of_eq ?_)
    push_cast
    ring
  obtain ⟨hlow, hhigh⟩ :=
    alternating_series_bracket_of_antitone_shift
      (f := fun k : ℕ ↦ x ^ (2 * k) / (Nat.factorial (2 * k) : ℝ)) N htend hfa
  rw [hsum] at hlow hhigh
  exact ⟨hlow, hhigh⟩
