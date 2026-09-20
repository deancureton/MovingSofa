import MovingSofa.ForMathlib.Analysis.SpecialFunctions.Trigonometric
import MovingSofa.Gerver.AreaCertificate

/-!
# Interval enclosures of the sine and cosine at scale `M`

The certificate evaluates the sine and the cosine by the interval Taylor recurrence
`GerverAreaCert.trigIter`, truncated at degree 41 and 40 and widened by one unit at scale
`M = 10 ^ 30`.  `trigZ_sound` is the soundness statement of that evaluator on `[0, 2]`: the
recurrence encloses the signed Taylor terms and their partial sums (`contains_trigIter`),
the alternating brackets of `Real.sin` and `Real.cos` control the truncation error by the
first omitted term, and `2 ^ 41 * 10 ^ 30 ≤ 41!` and `2 ^ 40 * 10 ^ 30 ≤ 40!` justify the
one-unit widening.
-/

namespace MovingSofa

open GerverAreaCert

/-! ### Sine and cosine enclosures -/

/-- The integer term recurrence encloses the signed Taylor terms and their partial
sums.  Pure interval arithmetic: an induction on `n` using the `SI` soundness lemmas. -/
theorem contains_trigIter {z t : SI} {x : ℝ} (hz : SI.Contains z (x * x))
    (ht : SI.Contains t x) (n : ℕ) :
    SI.Contains (trigIter z t n).1
        ((-1 : ℝ) ^ n * x ^ (2 * n + 1) / (Nat.factorial (2 * n + 1) : ℝ)) ∧
      SI.Contains (trigIter z t n).2.1
        ((-1 : ℝ) ^ n * x ^ (2 * n) / (Nat.factorial (2 * n) : ℝ)) ∧
      SI.Contains (trigIter z t n).2.2.1
        (∑ k ∈ Finset.range (n + 1),
          (-1 : ℝ) ^ k * x ^ (2 * k + 1) / (Nat.factorial (2 * k + 1) : ℝ)) ∧
      SI.Contains (trigIter z t n).2.2.2
        (∑ k ∈ Finset.range (n + 1),
          (-1 : ℝ) ^ k * x ^ (2 * k) / (Nat.factorial (2 * k) : ℝ)) := by
  induction n with
  | zero =>
    refine ⟨by simpa [trigIter] using ht, by simpa [trigIter] using SI.contains_one,
      by simpa [trigIter] using ht, ?_⟩
    simpa [trigIter] using SI.contains_one
  | succ n ih =>
    obtain ⟨ih1, ih2, ih3, ih4⟩ := ih
    have hfac1 : (Nat.factorial (2 * n + 1) : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
    have hfac2 : (Nat.factorial (2 * n) : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
    have hd1 : (0 : ℤ) < (((2 * n + 2) * (2 * n + 3) : ℕ) : ℤ) := by positivity
    have hd2 : (0 : ℤ) < (((2 * n + 1) * (2 * n + 2) : ℕ) : ℤ) := by positivity
    have hd1' : ((((2 * n + 2) * (2 * n + 3) : ℕ) : ℤ) : ℝ) ≠ 0 := by
      have : (0 : ℝ) < ((((2 * n + 2) * (2 * n + 3) : ℕ) : ℤ) : ℝ) := by exact_mod_cast hd1
      exact ne_of_gt this
    have hd2' : ((((2 * n + 1) * (2 * n + 2) : ℕ) : ℤ) : ℝ) ≠ 0 := by
      have : (0 : ℝ) < ((((2 * n + 1) * (2 * n + 2) : ℕ) : ℤ) : ℝ) := by exact_mod_cast hd2
      exact ne_of_gt this
    have e1 : (Nat.factorial (2 * (n + 1) + 1) : ℝ) =
        (Nat.factorial (2 * n + 1) : ℝ) * ((((2 * n + 2) * (2 * n + 3) : ℕ) : ℤ) : ℝ) := by
      have h : 2 * (n + 1) + 1 = 2 * n + 1 + 1 + 1 := by ring
      rw [h, Nat.factorial_succ, Nat.factorial_succ]
      push_cast
      ring
    have e2 : (Nat.factorial (2 * (n + 1)) : ℝ) =
        (Nat.factorial (2 * n) : ℝ) * ((((2 * n + 1) * (2 * n + 2) : ℕ) : ℤ) : ℝ) := by
      have h : 2 * (n + 1) = 2 * n + 1 + 1 := by ring
      rw [h, Nat.factorial_succ, Nat.factorial_succ]
      push_cast
      ring
    have v1 : -((((-1 : ℝ) ^ n * x ^ (2 * n + 1) / (Nat.factorial (2 * n + 1) : ℝ)) * (x * x)) /
          ((((2 * n + 2) * (2 * n + 3) : ℕ) : ℤ) : ℝ)) =
        (-1 : ℝ) ^ (n + 1) * x ^ (2 * (n + 1) + 1) /
          (Nat.factorial (2 * (n + 1) + 1) : ℝ) := by
      rw [e1, show x ^ (2 * (n + 1) + 1) = x ^ (2 * n + 1) * (x * x) by ring]
      field_simp
      ring
    have v2 : -((((-1 : ℝ) ^ n * x ^ (2 * n) / (Nat.factorial (2 * n) : ℝ)) * (x * x)) /
          ((((2 * n + 1) * (2 * n + 2) : ℕ) : ℤ) : ℝ)) =
        (-1 : ℝ) ^ (n + 1) * x ^ (2 * (n + 1)) / (Nat.factorial (2 * (n + 1)) : ℝ) := by
      rw [e2, show x ^ (2 * (n + 1)) = x ^ (2 * n) * (x * x) by ring]
      field_simp
      ring
    have hs : SI.Contains
        (SI.neg (SI.divn (SI.mul (trigIter z t n).1 z) (((2 * n + 2) * (2 * n + 3) : ℕ) : ℤ)))
        ((-1 : ℝ) ^ (n + 1) * x ^ (2 * (n + 1) + 1) /
          (Nat.factorial (2 * (n + 1) + 1) : ℝ)) := by
      rw [← v1]
      exact SI.contains_neg (SI.contains_divn hd1 (SI.contains_mul ih1 hz))
    have hc : SI.Contains
        (SI.neg (SI.divn (SI.mul (trigIter z t n).2.1 z) (((2 * n + 1) * (2 * n + 2) : ℕ) : ℤ)))
        ((-1 : ℝ) ^ (n + 1) * x ^ (2 * (n + 1)) / (Nat.factorial (2 * (n + 1)) : ℝ)) := by
      rw [← v2]
      exact SI.contains_neg (SI.contains_divn hd2 (SI.contains_mul ih2 hz))
    refine ⟨hs, hc, ?_, ?_⟩
    · rw [Finset.sum_range_succ]
      exact SI.contains_add ih3 hs
    · rw [Finset.sum_range_succ]
      exact SI.contains_add ih4 hc

/-- The degree-41 sine Taylor polynomial overshoots by at most `1 / M` on `[0, 2]`. -/
private theorem sin_taylor_bracket {x : ℝ} (hx0 : 0 ≤ x) (hx2 : x ≤ 2) :
    (∑ k ∈ Finset.range 21,
        (-1 : ℝ) ^ k * x ^ (2 * k + 1) / (Nat.factorial (2 * k + 1) : ℝ)) -
        1 / (M : ℝ) ≤ Real.sin x ∧
      Real.sin x ≤ ∑ k ∈ Finset.range 21,
        (-1 : ℝ) ^ k * x ^ (2 * k + 1) / (Nat.factorial (2 * k + 1) : ℝ) := by
  obtain ⟨hlow, hhigh⟩ := Real.sin_mem_Icc_taylor_sums 10 hx0 (by push_cast; nlinarith)
  simp only [show (2 * 10 + 1 : ℕ) = 21 from rfl, show (2 * 10 : ℕ) = 20 from rfl] at hlow hhigh
  refine ⟨?_, hhigh⟩
  have hsplit : (∑ k ∈ Finset.range 21,
      (-1 : ℝ) ^ k * x ^ (2 * k + 1) / (Nat.factorial (2 * k + 1) : ℝ))
      = (∑ k ∈ Finset.range 20,
        (-1 : ℝ) ^ k * x ^ (2 * k + 1) / (Nat.factorial (2 * k + 1) : ℝ))
        + x ^ 41 / (Nat.factorial 41 : ℝ) := by
    rw [show (21 : ℕ) = 20 + 1 from rfl, Finset.sum_range_succ]
    norm_num
  have htail : x ^ 41 / (Nat.factorial 41 : ℝ) ≤ 1 / (M : ℝ) := by
    have hMv : ((M : ℤ) : ℝ) = 10 ^ 30 := by norm_num [M]
    rw [hMv]
    calc x ^ 41 / (Nat.factorial 41 : ℝ) ≤ (2 : ℝ) ^ 41 / (Nat.factorial 41 : ℝ) := by gcongr
      _ ≤ 1 / 10 ^ 30 := by norm_num [Nat.factorial]
  rw [hsplit]
  linarith

/-- The degree-40 cosine Taylor polynomial overshoots by at most `1 / M` on `[0, 2]`. -/
private theorem cos_taylor_bracket {x : ℝ} (hx0 : 0 ≤ x) (hx2 : x ≤ 2) :
    (∑ k ∈ Finset.range 21,
        (-1 : ℝ) ^ k * x ^ (2 * k) / (Nat.factorial (2 * k) : ℝ)) -
        1 / (M : ℝ) ≤ Real.cos x ∧
      Real.cos x ≤ ∑ k ∈ Finset.range 21,
        (-1 : ℝ) ^ k * x ^ (2 * k) / (Nat.factorial (2 * k) : ℝ) := by
  obtain ⟨hlow, hhigh⟩ := Real.cos_mem_Icc_taylor_sums 10 hx0 (by push_cast; nlinarith)
  simp only [show (2 * 10 + 1 : ℕ) = 21 from rfl, show (2 * 10 : ℕ) = 20 from rfl] at hlow hhigh
  refine ⟨?_, hhigh⟩
  have hsplit : (∑ k ∈ Finset.range 21,
      (-1 : ℝ) ^ k * x ^ (2 * k) / (Nat.factorial (2 * k) : ℝ))
      = (∑ k ∈ Finset.range 20,
        (-1 : ℝ) ^ k * x ^ (2 * k) / (Nat.factorial (2 * k) : ℝ))
        + x ^ 40 / (Nat.factorial 40 : ℝ) := by
    rw [show (21 : ℕ) = 20 + 1 from rfl, Finset.sum_range_succ]
    norm_num
  have htail : x ^ 40 / (Nat.factorial 40 : ℝ) ≤ 1 / (M : ℝ) := by
    have hMv : ((M : ℤ) : ℝ) = 10 ^ 30 := by norm_num [M]
    rw [hMv]
    calc x ^ 40 / (Nat.factorial 40 : ℝ) ≤ (2 : ℝ) ^ 40 / (Nat.factorial 40 : ℝ) := by gcongr
      _ ≤ 1 / 10 ^ 30 := by norm_num [Nat.factorial]
  rw [hsplit]
  linarith

/-- Soundness of the executable sine/cosine enclosure on `[0, 2]`. -/
theorem trigZ_sound {t : SI} {x : ℝ} (ht : SI.Contains t x) (hx0 : 0 ≤ x) (hx2 : x ≤ 2) :
    SI.Contains (trigZ t).1 (Real.sin x) ∧ SI.Contains (trigZ t).2 (Real.cos x) := by
  have hM : (0 : ℝ) < (M : ℝ) := SI.Mpos
  have hMinv : (M : ℝ) * (1 / (M : ℝ)) = 1 := by field_simp
  have hwiden : ∀ (S : SI) (y v : ℝ), SI.Contains S v → v - 1 / (M : ℝ) ≤ y → y ≤ v →
      SI.Contains (⟨S.lo - 1, S.hi + 1⟩ : SI) y := by
    intro S y v hS h1 h2
    obtain ⟨ha, hb⟩ := hS
    have hlow : (M : ℝ) * v - 1 ≤ (M : ℝ) * y := by
      have h := mul_le_mul_of_nonneg_left h1 hM.le
      nlinarith [hMinv]
    have hhigh : (M : ℝ) * y ≤ (M : ℝ) * v := mul_le_mul_of_nonneg_left h2 hM.le
    refine ⟨?_, ?_⟩ <;> push_cast <;> linarith
  have h20 : (20 : ℕ) + 1 = 21 := by norm_num
  have hz : SI.Contains (SI.mul t t) (x * x) := SI.contains_mul ht ht
  obtain ⟨-, -, hS, hC⟩ := contains_trigIter hz ht 20
  rw [h20] at hS hC
  obtain ⟨hs1, hs2⟩ := sin_taylor_bracket hx0 hx2
  obtain ⟨hc1, hc2⟩ := cos_taylor_bracket hx0 hx2
  exact ⟨hwiden _ (Real.sin x) _ hS hs1 hs2, hwiden _ (Real.cos x) _ hC hc1 hc2⟩

end MovingSofa
