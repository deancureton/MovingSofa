import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace EuclideanSpace

/-- A rectangle with finite coordinate bounds is bounded in the Euclidean plane. -/
theorem isBounded_coordinate_rectangle (l r a b : ℝ) :
    Bornology.IsBounded {p : EuclideanSpace ℝ (Fin 2) | l ≤ p 0 ∧ p 0 ≤ r ∧ a ≤ p 1 ∧ p 1 ≤ b} := by
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨(|l| + |r|) + (|a| + |b|), ?_⟩
  rintro p ⟨hl, hr, ha, hb⟩
  have hx : |p 0| ≤ |l| + |r| := abs_le.mpr
    ⟨by linarith [neg_abs_le l, abs_nonneg r],
      by linarith [le_abs_self r, abs_nonneg l]⟩
  have hy : |p 1| ≤ |a| + |b| := abs_le.mpr
    ⟨by linarith [neg_abs_le a, abs_nonneg b],
      by linarith [le_abs_self b, abs_nonneg a]⟩
  have hx2 := (sq_le_sq₀ (abs_nonneg (p 0)) (by positivity)).mpr hx
  have hy2 := (sq_le_sq₀ (abs_nonneg (p 1)) (by positivity)).mpr hy
  have hn := EuclideanSpace.norm_sq_eq p
  simp only [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs] at hn hx2 hy2
  nlinarith [mul_nonneg (by positivity : 0 ≤ |l| + |r|)
    (by positivity : 0 ≤ |a| + |b|), norm_nonneg p,
    abs_nonneg l, abs_nonneg r, abs_nonneg a, abs_nonneg b]

end EuclideanSpace
