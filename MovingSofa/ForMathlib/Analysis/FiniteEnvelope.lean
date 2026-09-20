import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.List.MinMax
import Mathlib.Tactic

noncomputable section

namespace List

open Filter Topology

lemma abs_foldr_min_apply_sub_le (l : List (ℝ → ℝ)) (r L x z : ℝ) (hL : 0 ≤ L)
    (hl : ∀ f ∈ l, |f x - f z| ≤ L * |x - z|) :
    |l.foldr (fun f s ↦ min (f x) s) r -
        l.foldr (fun f s ↦ min (f z) s) r| ≤ L * |x - z| := by
  induction l with
  | nil => simpa using mul_nonneg hL (abs_nonneg (x - z))
  | cons f l ih =>
      simp only [List.foldr_cons]
      refine (abs_min_sub_min_le_max _ _ _ _).trans (max_le ?_ ?_)
      · exact hl f (by simp)
      · exact ih (fun g hg ↦ hl g (by simp [hg]))

lemma abs_foldr_max_apply_sub_le (l : List (ℝ → ℝ)) (r L x z : ℝ) (hL : 0 ≤ L)
    (hl : ∀ f ∈ l, |f x - f z| ≤ L * |x - z|) :
    |l.foldr (fun f s ↦ max (f x) s) r -
        l.foldr (fun f s ↦ max (f z) s) r| ≤ L * |x - z| := by
  induction l with
  | nil => simpa using mul_nonneg hL (abs_nonneg (x - z))
  | cons f l ih =>
      simp only [List.foldr_cons]
      refine (abs_max_sub_max_le_max _ _ _ _).trans (max_le ?_ ?_)
      · exact hl f (by simp)
      · exact ih (fun g hg ↦ hl g (by simp [hg]))

lemma le_foldr_min_apply_iff (l : List (ℝ → ℝ)) (r x y : ℝ) :
    y ≤ l.foldr (fun f s ↦ min (f x) s) r ↔ y ≤ r ∧ ∀ f ∈ l, y ≤ f x := by
  induction l with
  | nil => simp
  | cons f l ih => simp [ih, and_left_comm]

lemma foldr_max_apply_le_iff (l : List (ℝ → ℝ)) (r x y : ℝ) :
    l.foldr (fun f s ↦ max (f x) s) r ≤ y ↔ r ≤ y ∧ ∀ f ∈ l, f x ≤ y := by
  induction l with
  | nil => simp
  | cons f l ih => simp [ih, and_left_comm]

end List
