import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Triangular rearrangement of a double sum over a `Finset`

A double sum over `s ×ˢ s` splits into the closed lower triangle `{(u, t) | u ≤ t}` and its
transpose. The two pieces overlap exactly on the diagonal, so for a kernel vanishing there the
lower-triangular sum plus its transpose recovers the whole double sum.

`Finset.sum_sum_Ioi_add_eq_sum_sum_off_diag` is the `Fintype` and `LocallyFiniteOrder` analogue,
and `Fin.sum_sum_eq_sum_triangle_add` the `Fin` analogue; neither applies to a general `Finset`
of a plain `LinearOrder`.
-/

namespace Finset

variable {ι M : Type*} [LinearOrder ι] [AddCommMonoid M]

/-- For a kernel vanishing on the diagonal, the closed lower-triangular double sum plus the same
sum with the two arguments swapped is the full double sum. -/
theorem sum_filter_le_add_sum_filter_le_swap (s : Finset ι) (f : ι → ι → M)
    (hdiag : ∀ x, f x x = 0) :
    ((∑ t ∈ s, ∑ u ∈ s.filter (fun u ↦ u ≤ t), f u t) +
        ∑ t ∈ s, ∑ u ∈ s.filter (fun u ↦ u ≤ t), f t u) =
      ∑ x ∈ s, ∑ y ∈ s, f x y := by
  classical
  calc ((∑ t ∈ s, ∑ u ∈ s.filter (fun u ↦ u ≤ t), f u t) +
          ∑ t ∈ s, ∑ u ∈ s.filter (fun u ↦ u ≤ t), f t u)
      = (∑ t ∈ s, ∑ u ∈ s.filter (fun u ↦ t < u), f t u) +
          ∑ t ∈ s, ∑ u ∈ s.filter (fun u ↦ u ≤ t), f t u := by
        rw [Finset.sum_comm' (t' := s) (s' := fun u ↦ s.filter (fun t ↦ u ≤ t))
          (by simp; tauto)]
        refine congrArg₂ _ (Finset.sum_congr rfl fun t _ ↦ (Finset.sum_subset
          (monotone_filter_right _ fun _ _ ↦ le_of_lt) fun u hu hu' ↦ ?_).symm) rfl
        simp only [mem_filter, not_and, not_lt] at hu hu'
        rw [le_antisymm (hu' hu.1) hu.2, hdiag]
    _ = ∑ x ∈ s, ∑ y ∈ s, f x y := by
        rw [add_comm, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun x _ ↦ by
          simpa using Finset.sum_filter_add_sum_filter_not s (· ≤ x) (f x)

end Finset
