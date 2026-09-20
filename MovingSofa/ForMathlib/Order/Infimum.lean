import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Linarith

open Set

/-- Uniformly close real functions have uniformly close infima on a nonempty set. -/
theorem abs_sInf_image_sub_sInf_image_le {ι : Type*} {s : Set ι}
    (hs : s.Nonempty) (f g : ι → ℝ) (hf : BddBelow (f '' s)) (hg : BddBelow (g '' s))
    {C : ℝ} (h : ∀ x ∈ s, |f x - g x| ≤ C) :
    |sInf (f '' s) - sInf (g '' s)| ≤ C := by
  have hfg : sInf (f '' s) - C ≤ sInf (g '' s) := by
    apply le_csInf (hs.image g)
    rintro _ ⟨x, hx, rfl⟩
    have hfx : sInf (f '' s) ≤ f x := csInf_le hf ⟨x, hx, rfl⟩
    have hpoint := (abs_le.mp (h x hx)).2
    linarith
  have hgf : sInf (g '' s) - C ≤ sInf (f '' s) := by
    apply le_csInf (hs.image f)
    rintro _ ⟨x, hx, rfl⟩
    have hgx : sInf (g '' s) ≤ g x := csInf_le hg ⟨x, hx, rfl⟩
    have hpoint := (abs_le.mp (h x hx)).1
    linarith
  rw [abs_le]
  constructor <;> linarith
