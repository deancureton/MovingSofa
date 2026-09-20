import MovingSofa.Geometry.Frame
import Mathlib.Tactic.LinearCombination

noncomputable section

namespace MovingSofa

/-- A nontrivial segment has at most one normal direction strictly between zero and pi. -/
theorem eq_of_inner_sub_normalVector_eq_zero_of_ne {a b : Point} {s t : ℝ}
    (hs : s ∈ Set.Ioo 0 Real.pi) (ht : t ∈ Set.Ioo 0 Real.pi) (hab : a ≠ b)
    (horths : inner ℝ (b - a) (normalVector (s : Real.Angle)) = 0)
    (hortht : inner ℝ (b - a) (normalVector (t : Real.Angle)) = 0) : s = t := by
  have hs' : (b 0 - a 0) * Real.cos s + (b 1 - a 1) * Real.sin s = 0 := by
    simpa [normalVector, frame, PiLp.inner_apply, mul_comm] using horths
  have ht' : (b 0 - a 0) * Real.cos t + (b 1 - a 1) * Real.sin t = 0 := by
    simpa [normalVector, frame, PiLp.inner_apply, mul_comm] using hortht
  have hxprod : (b 0 - a 0) * Real.sin (s - t) = 0 := by
    rw [Real.sin_sub]
    linear_combination Real.sin s * ht' - Real.sin t * hs'
  have hyprod : (b 1 - a 1) * Real.sin (s - t) = 0 := by
    rw [Real.sin_sub]
    linear_combination Real.cos t * hs' - Real.cos s * ht'
  have hsin : Real.sin (s - t) = 0 := by
    by_contra hne
    have hx : b 0 = a 0 := by
      exact sub_eq_zero.mp ((mul_eq_zero.mp hxprod).resolve_right hne)
    have hy : b 1 = a 1 := by
      exact sub_eq_zero.mp ((mul_eq_zero.mp hyprod).resolve_right hne)
    apply hab
    ext i
    fin_cases i
    · exact hx.symm
    · exact hy.symm
  have hz := (Real.sin_eq_zero_iff_of_lt_of_lt
    (by linarith [hs.1, ht.2]) (by linarith [hs.2, ht.1])).mp hsin
  linarith

/-- Normal lines with angles strictly between zero and pi agree exactly when their data agree. -/
theorem normalLine_eq_iff_of_mem_Ioo {s t c d : ℝ}
    (hs : s ∈ Set.Ioo 0 Real.pi) (ht : t ∈ Set.Ioo 0 Real.pi) :
    normalLine (s : Real.Angle) c = normalLine (t : Real.Angle) d ↔
      s = t ∧ c = d := by
  constructor
  · intro hline
    let p := c • normalVector (s : Real.Angle)
    let q := p + tangentVector (s : Real.Angle)
    have hp : p ∈ normalLine (s : Real.Angle) c := by
      change inner ℝ p (normalVector (s : Real.Angle)) = c
      rw [show p = c • normalVector (s : Real.Angle) by rfl,
        real_inner_smul_left, inner_normalVector_self]
      simp
    have hq : q ∈ normalLine (s : Real.Angle) c := by
      change inner ℝ q (normalVector (s : Real.Angle)) = c
      rw [show q = p + tangentVector (s : Real.Angle) by rfl, inner_add_left]
      rw [show inner ℝ p (normalVector (s : Real.Angle)) = c by exact hp]
      rw [real_inner_comm, inner_normalVector_tangentVector, add_zero]
    have hp' : p ∈ normalLine (t : Real.Angle) d := hline ▸ hp
    have hq' : q ∈ normalLine (t : Real.Angle) d := hline ▸ hq
    have hv : tangentVector (s : Real.Angle) ≠ 0 := by
      intro hz
      have hinner := inner_tangentVector_self s
      rw [hz, inner_zero_left] at hinner
      norm_num at hinner
    have hsorth : inner ℝ (tangentVector (s : Real.Angle))
        (normalVector (s : Real.Angle)) = 0 := by
      rw [real_inner_comm, inner_normalVector_tangentVector]
    have htorth : inner ℝ (tangentVector (s : Real.Angle))
        (normalVector (t : Real.Angle)) = 0 := by
      rw [show tangentVector (s : Real.Angle) = q - p by simp [q]]
      rw [inner_sub_left, show inner ℝ q (normalVector (t : Real.Angle)) = d by exact hq',
        show inner ℝ p (normalVector (t : Real.Angle)) = d by exact hp', sub_self]
    have hst := eq_of_inner_sub_normalVector_eq_zero_of_ne
      (a := 0) (b := tangentVector (s : Real.Angle)) hs ht hv.symm
      (by simpa using hsorth) (by simpa using htorth)
    subst t
    refine ⟨rfl, ?_⟩
    change inner ℝ p (normalVector (s : Real.Angle)) = d at hp'
    rw [show inner ℝ p (normalVector (s : Real.Angle)) = c by exact hp] at hp'
    exact hp'
  · rintro ⟨rfl, rfl⟩
    rfl

/-- Opposite normal angles describe the same line with the opposite offset. -/
theorem normalLine_eq_of_cut {a b c : ℝ}
    (hab : ((b : ℝ) : Real.Angle) = ((a + Real.pi : ℝ) : Real.Angle)) :
    normalLine ((b : ℝ) : Real.Angle) c = normalLine ((a : ℝ) : Real.Angle) (-c) := by
  rw [hab]
  ext p
  simp only [normalLine, Set.mem_ofPred_eq, normalVector_add_pi, inner_neg_right]
  constructor <;> intro h <;> linarith only [h]
end MovingSofa
