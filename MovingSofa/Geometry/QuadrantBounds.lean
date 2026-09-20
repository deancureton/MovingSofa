import MovingSofa.Geometry.Frame
import MovingSofa.ForMathlib.Analysis.InnerProductSpace.Box

namespace MovingSofa

/-- A horizontal lower bound cuts a first-quadrant pair of upper projection bounds to a bounded set. -/
theorem isBounded_setOf_le_snd_and_inner_lt (a b c t : ℝ) (ht : t ∈ Set.Ioo 0 (Real.pi / 2)) :
    Bornology.IsBounded {p : Point | a ≤ p 1 ∧
      inner ℝ p (normalVector (t : Real.Angle)) < b ∧
      inner ℝ p (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) < c} := by
  have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht.1
    (ht.2.trans (by linarith [Real.pi_pos]))
  have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩
  apply (EuclideanSpace.isBounded_coordinate_rectangle ((Real.cos t * a - c) / Real.sin t)
    ((b - Real.sin t * a) / Real.cos t) a (Real.sin t * b + Real.cos t * c)).subset
  rintro p ⟨hy, h₁, h₂⟩
  have hb : Real.cos t * p 0 + Real.sin t * p 1 < b := by
    simpa [normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two, mul_comm] using h₁
  have hd : -Real.sin t * p 0 + Real.cos t * p 1 < c := by
    simpa [normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two,
      Real.cos_add, Real.sin_add, -Real.Angle.coe_add, mul_comm] using h₂
  refine ⟨?_, ?_, hy, ?_⟩
  · apply (div_le_iff₀ hs).2
    nlinarith only [hd, mul_le_mul_of_nonneg_left hy hc.le]
  · apply (le_div_iff₀ hc).2
    nlinarith only [hb, mul_le_mul_of_nonneg_left hy hs.le]
  · have hyid : (Real.sin t ^ 2 + Real.cos t ^ 2) * p 1 = p 1 := by
      rw [Real.sin_sq_add_cos_sq, one_mul]
    have hb' := mul_lt_mul_of_pos_left hb hs
    have hd' := mul_lt_mul_of_pos_left hd hc
    nlinarith only [hyid, hb', hd']

end MovingSofa
