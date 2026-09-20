import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

noncomputable section

namespace Fin

/-- A finite sequence is bounded by its final value plus its positive backward increments. -/
theorem apply_le_last_add_sum_max_sub {n : ℕ} (f : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    f i ≤ f (Fin.last n) + ∑ j : Fin n, max (f j.castSucc - f j.succ) 0 := by
  induction n with
  | zero => fin_cases i; simp
  | succ n ih =>
    rw [Fin.sum_univ_succ]
    have htail (k : Fin (n + 1)) := ih (fun j ↦ f j.succ) k
    have hnonneg : 0 ≤ max (f 0 - f (Fin.succ 0)) 0 := le_max_right _ _
    refine Fin.cases ?_ (fun k ↦ ?_) i
    · have h := htail 0
      have hmax := le_max_left (f 0 - f (Fin.succ 0)) 0
      simpa only [Fin.succ_last, Fin.succ_castSucc, Fin.castSucc_zero] using
        (show f 0 ≤ f (Fin.last (n + 1)) +
          (max (f 0 - f (Fin.succ 0)) 0 +
            ∑ j : Fin n, max (f j.castSucc.succ - f j.succ.succ) 0) by
          simp only [Fin.succ_last] at h
          linarith)
    · have h := htail k
      simpa only [Fin.succ_last, Fin.succ_castSucc, Fin.castSucc_zero] using
        (show f k.succ ≤ f (Fin.last (n + 1)) +
          (max (f 0 - f (Fin.succ 0)) 0 +
            ∑ j : Fin n, max (f j.castSucc.succ - f j.succ.succ) 0) by
          simp only [Fin.succ_last] at h
          linarith)

end Fin
