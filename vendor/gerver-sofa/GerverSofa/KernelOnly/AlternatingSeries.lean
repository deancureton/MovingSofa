import GerverSofa.ExactReplay
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Alternating-series kernel for the executable transcendental layer

This file connects the exact rational partial sums used by `ExactReplay` to
Mathlib's real power-series theorems.  The Taylor evaluator is intentionally
used only on arguments in `[0, 1]`; the range-reduction layer proves this
precondition before calling these results.
-/

noncomputable section

namespace GerverSofa.ExactReplay

open scoped BigOperators
open Filter Finset

/-- Real magnitude of the `n`th sine-series term. -/
def sinMagnitude (x : ℝ) (n : ℕ) : ℝ :=
  x ^ (2 * n + 1) / (Nat.factorial (2 * n + 1) : ℝ)

/-- Real magnitude of the `n`th cosine-series term. -/
def cosMagnitude (x : ℝ) (n : ℕ) : ℝ :=
  x ^ (2 * n) / (Nat.factorial (2 * n) : ℝ)

/-- Real magnitude of the `n`th arctangent-series term. -/
def atanMagnitude (x : ℝ) (n : ℕ) : ℝ :=
  x ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ)

/-- On `[0,1]`, the unsigned sine Taylor terms decrease. -/
theorem antitone_sinMagnitude {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Antitone (sinMagnitude x) := by
  apply antitone_nat_of_succ_le
  intro n
  simp only [sinMagnitude]
  refine div_le_div₀ (pow_nonneg hx0 _) ?_ (by positivity) ?_
  · exact pow_le_pow_of_le_one hx0 hx1 (by omega)
  · exact_mod_cast Nat.factorial_le (by omega)

/-- On `[0,1]`, the unsigned cosine Taylor terms decrease. -/
theorem antitone_cosMagnitude {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Antitone (cosMagnitude x) := by
  apply antitone_nat_of_succ_le
  intro n
  simp only [cosMagnitude]
  refine div_le_div₀ (pow_nonneg hx0 _) ?_ (by positivity) ?_
  · exact pow_le_pow_of_le_one hx0 hx1 (by omega)
  · exact_mod_cast Nat.factorial_le (by omega)

/-- On `[0,1]`, the unsigned arctangent Taylor terms decrease. -/
theorem antitone_atanMagnitude {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Antitone (atanMagnitude x) := by
  apply antitone_nat_of_succ_le
  intro n
  simp only [atanMagnitude]
  refine div_le_div₀ (pow_nonneg hx0 _) ?_ (by positivity) ?_
  · exact pow_le_pow_of_le_one hx0 hx1 (by omega)
  · exact_mod_cast (show 2 * n + 1 ≤ 2 * (n + 1) + 1 by omega)

/-- Casting the executable sine partial sum to `ℝ` gives the corresponding
Mathlib finite Taylor sum. -/
theorem coe_sinPartial (x : ℚ) (terms : ℕ) :
    ((GerverSofa.ExactReplay.sinPartial x terms : ℚ) : ℝ) =
      ∑ k ∈ Finset.range terms,
        (-1 : ℝ) ^ k * (x : ℝ) ^ (2 * k + 1) /
          (Nat.factorial (2 * k + 1) : ℝ) := by
  simp [GerverSofa.ExactReplay.sinPartial, GerverSofa.ExactReplay.signedTerm,
    GerverSofa.ExactReplay.factorialQ, neg_one_pow_eq_ite, Nat.even_iff]
  refine Finset.sum_congr rfl ?_
  intro k hk
  by_cases h : k % 2 = 0 <;> simp [h, neg_div]

/-- Casting the executable cosine partial sum to `ℝ` gives the corresponding
Mathlib finite Taylor sum. -/
theorem coe_cosPartial (x : ℚ) (terms : ℕ) :
    ((GerverSofa.ExactReplay.cosPartial x terms : ℚ) : ℝ) =
      ∑ k ∈ Finset.range terms,
        (-1 : ℝ) ^ k * (x : ℝ) ^ (2 * k) /
          (Nat.factorial (2 * k) : ℝ) := by
  simp [GerverSofa.ExactReplay.cosPartial, GerverSofa.ExactReplay.signedTerm,
    GerverSofa.ExactReplay.factorialQ, neg_one_pow_eq_ite, Nat.even_iff]
  refine Finset.sum_congr rfl ?_
  intro k hk
  by_cases h : k % 2 = 0 <;> simp [h, neg_div]

/-- Casting the executable arctangent partial sum to `ℝ` gives the
corresponding Mathlib finite Taylor sum. -/
theorem coe_atanPartial (x : ℚ) (terms : ℕ) :
    ((GerverSofa.ExactReplay.atanPartial x terms : ℚ) : ℝ) =
      ∑ k ∈ Finset.range terms,
        (-1 : ℝ) ^ k * (x : ℝ) ^ (2 * k + 1) /
          ((2 * k + 1 : ℕ) : ℝ) := by
  simp [GerverSofa.ExactReplay.atanPartial, neg_one_pow_eq_ite, Nat.even_iff]
  refine Finset.sum_congr rfl ?_
  intro k hk
  by_cases h : k % 2 = 0 <;> simp [h, neg_div]

/-- The 20-term sine partial sum is a lower bound and the 19-term partial sum
is an upper bound for every rational argument in `[0,1]`. -/
theorem sine_between_partials {x : ℚ}
    (hx0 : (0 : ℚ) ≤ x) (hx1 : x ≤ 1) :
    ((GerverSofa.ExactReplay.sinPartial x 20 : ℚ) : ℝ) ≤ Real.sin (x : ℝ) ∧
      Real.sin (x : ℝ) ≤ ((GerverSofa.ExactReplay.sinPartial x 19 : ℚ) : ℝ) := by
  have hx0r : (0 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx0
  have hx1r : (x : ℝ) ≤ 1 := by exact_mod_cast hx1
  have hanti : Antitone (sinMagnitude (x : ℝ)) :=
    antitone_sinMagnitude hx0r hx1r
  have htendRaw := (Real.hasSum_sin (x : ℝ)).tendsto_sum_nat
  have htendMag :
      Filter.Tendsto
        (fun n : ℕ => ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * sinMagnitude (x : ℝ) i)
        Filter.atTop (nhds (Real.sin (x : ℝ))) := by
    simpa only [sinMagnitude, mul_div_assoc] using htendRaw
  have hlower := Antitone.alternating_series_le_tendsto htendMag hanti 10
  have hupper := Antitone.tendsto_le_alternating_series htendMag hanti 9
  have h20 : (2 * 10 : ℕ) = 20 := by norm_num
  have h19 : (2 * 9 + 1 : ℕ) = 19 := by norm_num
  constructor
  · rw [coe_sinPartial]
    simpa only [sinMagnitude, mul_div_assoc, h20] using hlower
  · rw [coe_sinPartial]
    simpa only [sinMagnitude, mul_div_assoc, h19] using hupper

/-- The 20-term cosine partial sum is a lower bound and the 19-term partial
sum is an upper bound for every rational argument in `[0,1]`. -/
theorem cosine_between_partials {x : ℚ}
    (hx0 : (0 : ℚ) ≤ x) (hx1 : x ≤ 1) :
    ((GerverSofa.ExactReplay.cosPartial x 20 : ℚ) : ℝ) ≤ Real.cos (x : ℝ) ∧
      Real.cos (x : ℝ) ≤ ((GerverSofa.ExactReplay.cosPartial x 19 : ℚ) : ℝ) := by
  have hx0r : (0 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx0
  have hx1r : (x : ℝ) ≤ 1 := by exact_mod_cast hx1
  have hanti : Antitone (cosMagnitude (x : ℝ)) :=
    antitone_cosMagnitude hx0r hx1r
  have htendRaw := (Real.hasSum_cos (x : ℝ)).tendsto_sum_nat
  have htendMag :
      Filter.Tendsto
        (fun n : ℕ => ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * cosMagnitude (x : ℝ) i)
        Filter.atTop (nhds (Real.cos (x : ℝ))) := by
    simpa only [cosMagnitude, mul_div_assoc] using htendRaw
  have hlower := Antitone.alternating_series_le_tendsto htendMag hanti 10
  have hupper := Antitone.tendsto_le_alternating_series htendMag hanti 9
  have h20 : (2 * 10 : ℕ) = 20 := by norm_num
  have h19 : (2 * 9 + 1 : ℕ) = 19 := by norm_num
  constructor
  · rw [coe_cosPartial]
    simpa only [cosMagnitude, mul_div_assoc, h20] using hlower
  · rw [coe_cosPartial]
    simpa only [cosMagnitude, mul_div_assoc, h19] using hupper

/-- Even/odd arctangent partial sums provide certified lower/upper bounds. -/
theorem arctan_between_partials {x : ℚ}
    (hx0 : (0 : ℚ) ≤ x) (hx1 : x < 1) (k : ℕ) :
    ((GerverSofa.ExactReplay.atanPartial x (2 * k + 2) : ℚ) : ℝ) ≤ Real.arctan (x : ℝ) ∧
      Real.arctan (x : ℝ) ≤ ((GerverSofa.ExactReplay.atanPartial x (2 * k + 1) : ℚ) : ℝ) := by
  have hx0r : (0 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx0
  have hx1r : (x : ℝ) < 1 := by exact_mod_cast hx1
  have hx1le : (x : ℝ) ≤ 1 := hx1r.le
  have habs : ‖(x : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hx0r]
    exact hx1r
  have hanti : Antitone (atanMagnitude (x : ℝ)) :=
    antitone_atanMagnitude hx0r hx1le
  have htendRaw := (Real.hasSum_arctan habs).tendsto_sum_nat
  have htendMag :
      Filter.Tendsto
        (fun n : ℕ => ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * atanMagnitude (x : ℝ) i)
        Filter.atTop (nhds (Real.arctan (x : ℝ))) := by
    simpa only [atanMagnitude, mul_div_assoc] using htendRaw
  have hlower := Antitone.alternating_series_le_tendsto htendMag hanti (k + 1)
  have hupper := Antitone.tendsto_le_alternating_series htendMag hanti k
  constructor
  · rw [coe_atanPartial]
    have hidx : 2 * (k + 1) = 2 * k + 2 := by omega
    simpa only [atanMagnitude, mul_div_assoc, hidx] using hlower
  · rw [coe_atanPartial]
    simpa only [atanMagnitude, mul_div_assoc] using hupper

end GerverSofa.ExactReplay
