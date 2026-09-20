import Mathlib.Analysis.Convex.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

namespace Convex

/-- Every nonnegative scalar between zero and a known scalar multiple stays in a convex set. -/
theorem smul_mem_of_nonneg_of_le {E : Type*} [AddCommGroup E] [Module ℝ E]
    {s : Set E} (hs : Convex ℝ s) {v : E} {x a : ℝ}
    (hzero : (0 : E) ∈ s) (ha : a • v ∈ s) (hx : 0 ≤ x) (hxa : x ≤ a) :
    x • v ∈ s := by
  by_cases ha0 : a = 0
  · have hx0 : x = 0 := by linarith
    simpa [hx0] using hzero
  · have hapos : 0 < a := lt_of_le_of_ne (hx.trans hxa) (Ne.symm ha0)
    have hratio : x / a ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨div_nonneg hx hapos.le, (div_le_one hapos).2 hxa⟩
    have hmem := hs.smul_mem_of_zero_mem hzero ha hratio
    simpa only [smul_smul, div_mul_cancel₀ x ha0] using hmem

end Convex
