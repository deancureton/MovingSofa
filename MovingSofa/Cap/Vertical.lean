import MovingSofa.Cap.HalfPlanes

noncomputable section

namespace MovingSofa

/-- A cap is closed under downward vertical movement that remains inside its fan. -/
theorem CapSpace.mem_of_fst_eq_of_snd_le {ω : ℝ} (K : CapSpace ω)
    {p q : Point} (hp : p ∈ (K.val : Set Point)) (hq : q ∈ capFan ω)
    (hx : q 0 = p 0) (hy : q 1 ≤ p 1) : q ∈ (K.val : Set Point) := by
  apply K.mem_of_mem_capFan_of_le_supportValue hq
  intro t ht
  apply le_trans _ (inner_le_supportValue K.val hp (t : Real.Angle))
  have htI : t ∈ Set.Icc 0 Real.pi := by
    rcases ht with ht | ht
    · exact ⟨ht.1, by linarith [ht.2, K.property.2.1, Real.pi_pos]⟩
    · exact ⟨by linarith [ht.1, Real.pi_pos], by linarith [ht.2, K.property.2.1]⟩
  have h := mul_le_mul_of_nonneg_left hy (Real.sin_nonneg_of_mem_Icc htI)
  simp [normalVector, frame, PiLp.inner_apply, hx]
  linarith

end MovingSofa
