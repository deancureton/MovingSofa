import MovingSofa.Cap.Basic
import Mathlib.Tactic.Linarith

noncomputable section

namespace MovingSofa

/-- Every upper normal of an angle set has strictly positive sine. -/
lemma angleDomain_subset_Ioo (Θ : AngleSet) : angleDomain Θ ⊆ Set.Ioo 0 Real.pi := by
  intro t ht
  rcases ht with (ht | ⟨s, hs, rfl⟩) | ht
  · have h := Θ.interior t ht
    constructor <;> linarith [h.1, h.2, Θ.angle_le, Real.pi_pos]
  · have h := Θ.interior s hs
    constructor <;> linarith [h.1, h.2, Θ.angle_le, Real.pi_pos]
  · rcases ht with rfl | ht
    · constructor <;> linarith [Θ.angle_pos, Θ.angle_le, Real.pi_pos]
    · have ht : t = Real.pi / 2 := ht
      rw [ht]
      constructor <;> linarith [Real.pi_pos]

end MovingSofa
