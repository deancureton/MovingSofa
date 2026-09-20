import Mathlib.Order.SuccPred.LinearLocallyFinite

import Mathlib.Data.Fin.SuccPredOrder

import Mathlib.Order.SuccPred.IntervalSucc
import Mathlib.Order.Fin.Basic

open Set

/-- Adjacent half-open intervals of a finite monotone sequence cover its endpoint interval. -/
theorem Monotone.iUnion_Ioc_fin {α : Type*} [LinearOrder α] {n : ℕ} (cuts : Fin (n+1) → α)
    (hcuts : Monotone cuts) :
    (⋃ i : Fin n, Ioc (cuts i.castSucc) (cuts i.succ)) = Ioc (cuts 0) (cuts (Fin.last n)) := by
  rw [← hcuts.biUnion_Ico_Ioc_map_succ 0 (Fin.last n)]
  ext x
  simp only [mem_iUnion]
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i.castSucc, ⟨Fin.zero_le _, i.castSucc_lt_last⟩, ?_⟩
    simpa only [Fin.orderSucc_castSucc] using hi
  · rintro ⟨i, hi, hx⟩
    have hn : i.val < n := hi.2
    refine ⟨⟨i, hn⟩, ?_⟩
    change x ∈ Ioc (cuts (⟨i, hn⟩ : Fin n).castSucc)
      (cuts (Order.succ (⟨i, hn⟩ : Fin n).castSucc)) at hx
    simpa only [Fin.orderSucc_castSucc] using hx
