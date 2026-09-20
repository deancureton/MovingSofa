import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Calculus.MeanValue

/-!
# A cubic remainder bound for the arctangent

`Real.abs_arctan_sub_self_le` complements `Real.abs_arctan_le_abs` by quantifying the
first-order approximation `arctan s ≈ s` near the origin.
-/

namespace Real

/-- The arctangent differs from the identity by at most a cubic error. -/
theorem abs_arctan_sub_self_le (s : ℝ) : |arctan s - s| ≤ |s| ^ 3 := by
  have hderiv : ∀ u ∈ Set.uIcc (0 : ℝ) s,
      HasDerivWithinAt (fun u : ℝ ↦ arctan u - u) (1 / (1 + u ^ 2) - 1)
        (Set.uIcc (0 : ℝ) s) u := fun u _ ↦
    ((hasDerivAt_arctan u).sub (hasDerivAt_id u)).hasDerivWithinAt
  have hbound : ∀ u ∈ Set.uIcc (0 : ℝ) s, ‖1 / (1 + u ^ 2) - 1‖ ≤ s ^ 2 := by
    intro u hu
    have hu' : |u| ≤ |s| := by
      rcases Set.mem_uIcc.mp hu with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
        rcases abs_cases u with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;>
          rcases abs_cases s with ⟨f1, f2⟩ | ⟨f1, f2⟩ <;> linarith
    have hpos : (0 : ℝ) < 1 + u ^ 2 := by positivity
    have heq : 1 / (1 + u ^ 2) - 1 = -(u ^ 2 / (1 + u ^ 2)) := by field_simp; ring
    rw [heq, norm_neg, Real.norm_eq_abs, abs_of_nonneg (by positivity), div_le_iff₀ hpos]
    nlinarith [sq_abs u, sq_abs s, abs_nonneg u, abs_nonneg s, sq_nonneg u]
  have hmain := (convex_uIcc (0 : ℝ) s).norm_image_sub_le_of_norm_hasDerivWithin_le
    hderiv hbound Set.left_mem_uIcc Set.right_mem_uIcc
  have hmain' : |arctan s - s| ≤ s ^ 2 * |s| := by simpa using hmain
  calc |arctan s - s| ≤ s ^ 2 * |s| := hmain'
    _ = |s| ^ 3 := by rw [← sq_abs s]; ring

/-- First-order angle estimate. If `W = (w0, w1)` has norm `nw > 0` and the displacement
`d = (d0, d1)` has norm `nd` with `2 * nd ≤ nw`, then the principal angle between `W` and
`W + d`, in the arctangent form given by their cross and dot products, differs from its
linearization `(w0 * d1 - w1 * d0) / nw ^ 2` by at most `6 * nd ^ 2 / nw ^ 2`. -/
theorem abs_arctan_div_sub_le_of_small {w0 w1 d0 d1 nw nd : ℝ}
    (hnw : 0 < nw) (hnw2 : nw ^ 2 = w0 ^ 2 + w1 ^ 2)
    (hnd : 0 ≤ nd) (hnd2 : nd ^ 2 = d0 ^ 2 + d1 ^ 2)
    (hsmall : 2 * nd ≤ nw) :
    |arctan ((w0 * d1 - w1 * d0) / (nw ^ 2 + (w0 * d0 + w1 * d1))) -
        (w0 * d1 - w1 * d0) / nw ^ 2| ≤ 6 * nd ^ 2 / nw ^ 2 := by
  set N := w0 * d1 - w1 * d0 with hN
  set P := w0 * d0 + w1 * d1 with hP
  have hlag : N ^ 2 + P ^ 2 = nw ^ 2 * nd ^ 2 := by
    rw [hN, hP, hnw2, hnd2]; ring
  have hprod : 0 ≤ nw * nd := mul_nonneg hnw.le hnd
  have hCS : |N| ≤ nw * nd := by
    nlinarith [sq_abs N, abs_nonneg N, sq_nonneg P]
  have hCS' : |P| ≤ nw * nd := by
    nlinarith [sq_abs P, abs_nonneg P, sq_nonneg N]
  set D := nw ^ 2 + P with hD
  have hPlow : -(nw * nd) ≤ P := neg_le_of_abs_le hCS'
  have hDlow : nw ^ 2 / 2 ≤ D := by nlinarith
  have hD0 : 0 < D := lt_of_lt_of_le (by positivity) hDlow
  set s := N / D with hs
  have hsle : |s| ≤ 2 * nd / nw := by
    rw [hs, abs_div, abs_of_pos hD0, div_le_div_iff₀ hD0 hnw]
    nlinarith [abs_nonneg N]
  have hs1 : |s| ≤ 1 := by
    refine hsle.trans ?_
    rw [div_le_one hnw]
    linarith
  have h1 : |arctan s - s| ≤ 4 * nd ^ 2 / nw ^ 2 := by
    refine (abs_arctan_sub_self_le s).trans ?_
    have hstep : |s| ^ 3 ≤ (2 * nd / nw) ^ 2 := by
      nlinarith [abs_nonneg s, hsle, hs1, sq_nonneg (|s|)]
    refine hstep.trans_eq ?_
    field_simp
    ring
  have h2 : |s - N / nw ^ 2| ≤ 2 * nd ^ 2 / nw ^ 2 := by
    have heq : s - N / nw ^ 2 = -(N * P) / (D * nw ^ 2) := by
      rw [hs, hD]
      rw [div_sub_div _ _ (ne_of_gt hD0) (by positivity : (nw : ℝ) ^ 2 ≠ 0)]
      rw [hD]
      ring_nf
    rw [heq, abs_div, abs_neg, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < D * nw ^ 2),
      div_le_div_iff₀ (by positivity) (by positivity : (0 : ℝ) < nw ^ 2)]
    nlinarith [mul_le_mul hCS hCS' (abs_nonneg P) hprod, abs_nonneg N, abs_nonneg P,
      mul_nonneg (abs_nonneg N) (abs_nonneg P), sq_nonneg nd, sq_nonneg nw]
  calc |arctan s - N / nw ^ 2| ≤ |arctan s - s| + |s - N / nw ^ 2| :=
        abs_sub_le _ _ _
    _ ≤ 4 * nd ^ 2 / nw ^ 2 + 2 * nd ^ 2 / nw ^ 2 := add_le_add h1 h2
    _ = 6 * nd ^ 2 / nw ^ 2 := by ring

end Real
