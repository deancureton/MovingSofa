import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Two-sided bracketing of an alternating series with an antitone tail

`alternating_series_bracket_of_antitone_shift` upgrades the one-sided Leibniz estimates
`Antitone.alternating_series_le_tendsto` and `Antitone.tendsto_le_alternating_series` to a
two-sided bracket for an alternating series whose term magnitudes are antitone only from an
even index `2 * N` onwards: the sum then lies between the partial sums of `2 * N` and of
`2 * N + 1` terms.  `antitone_pow_div_factorial_two_mul_add` is the antitonicity criterion
for the stride-two factorial quotients `x ^ (2 * n + a) / (2 * n + a)!` that the Taylor
series of the trigonometric functions produce.
-/

/-- The stride-two factorial quotients `x ^ (2 * n + a) / (2 * n + a)!` are antitone as soon
as `x ^ 2 ≤ (a + 1) * (a + 2)`, i.e. as soon as the first term ratio is at most one. -/
theorem antitone_pow_div_factorial_two_mul_add {x : ℝ} (hx0 : 0 ≤ x) {a : ℕ}
    (hx : x ^ 2 ≤ ((a + 1) * (a + 2) : ℕ)) :
    Antitone fun n : ℕ ↦ x ^ (2 * n + a) / (Nat.factorial (2 * n + a) : ℝ) := by
  refine antitone_nat_of_succ_le fun n ↦ ?_
  set m := 2 * n + a with hm
  have ham : a ≤ m := by omega
  have hstep : 2 * (n + 1) + a = m + 1 + 1 := by omega
  have hfac : (0 : ℝ) < (Nat.factorial m : ℝ) := by positivity
  have hle : x ^ 2 ≤ ((m : ℝ) + 1) * ((m : ℝ) + 2) := by
    refine hx.trans ?_
    have hcast : (a : ℝ) ≤ (m : ℝ) := by exact_mod_cast ham
    have h0 : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
    push_cast
    nlinarith
  have hpow : x ^ (m + 1 + 1) = x ^ m * x * x := by ring
  rw [hstep, Nat.factorial_succ, Nat.factorial_succ, hpow,
    div_le_div_iff₀ (by positivity) hfac]
  push_cast
  nlinarith [mul_nonneg (mul_nonneg (pow_nonneg hx0 m) hfac.le) (sub_nonneg.2 hle)]

/-- Leibniz bracketing for an alternating series whose term magnitudes are antitone only
from index `2 * N` onwards: the limit lies between the partial sums of `2 * N` and of
`2 * N + 1` terms. -/
theorem alternating_series_bracket_of_antitone_shift {f : ℕ → ℝ} {l : ℝ} (N : ℕ)
    (hfl : Filter.Tendsto (fun n ↦ ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * f i)
      Filter.atTop (nhds l))
    (hfa : Antitone fun n ↦ f (2 * N + n)) :
    (∑ i ∈ Finset.range (2 * N), (-1 : ℝ) ^ i * f i) ≤ l ∧
      l ≤ ∑ i ∈ Finset.range (2 * N + 1), (-1 : ℝ) ^ i * f i := by
  set S := ∑ i ∈ Finset.range (2 * N), (-1 : ℝ) ^ i * f i with hS
  have key : ∀ n : ℕ, (∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * f (2 * N + i))
      = (∑ i ∈ Finset.range (2 * N + n), (-1 : ℝ) ^ i * f i) - S := by
    intro n
    rw [hS, Finset.sum_range_add]
    simp [pow_add, pow_mul]
  have hshift : Filter.Tendsto
      (fun n ↦ ∑ i ∈ Finset.range (2 * N + n), (-1 : ℝ) ^ i * f i)
      Filter.atTop (nhds l) := by
    have h := hfl.comp (Filter.tendsto_add_atTop_nat (2 * N))
    simpa [Function.comp_def, Nat.add_comm] using h
  have htend : Filter.Tendsto
      (fun n ↦ ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * f (2 * N + i))
      Filter.atTop (nhds (l - S)) := by
    simp only [key]
    exact hshift.sub_const S
  have hlow := Antitone.alternating_series_le_tendsto htend hfa 0
  have hhigh := Antitone.tendsto_le_alternating_series htend hfa 0
  simp only [Nat.mul_zero, Finset.range_zero, Finset.sum_empty, Nat.zero_add,
    Finset.sum_range_one, pow_zero, one_mul, Nat.add_zero] at hlow hhigh
  refine ⟨by linarith, ?_⟩
  rw [Finset.sum_range_succ, ← hS, pow_mul]
  simp only [neg_one_sq, one_pow, one_mul]
  linarith
