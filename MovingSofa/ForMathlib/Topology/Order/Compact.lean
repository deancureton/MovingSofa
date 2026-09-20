import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Algebra.Ring.Real

/-- A positive continuous function has a positive uniform lower bound on a nonempty compact set. -/
theorem IsCompact.exists_pos_forall_le {X : Type*} [TopologicalSpace X]
    {s : Set X} (hs : IsCompact s) (hne : s.Nonempty) {f : X → ℝ}
    (hf : ContinuousOn f s) (hpos : ∀ x ∈ s, 0 < f x) :
    ∃ m > 0, ∀ x ∈ s, m ≤ f x := by
  obtain ⟨x, hx, hxmin⟩ := hs.exists_isMinOn hne hf
  exact ⟨f x, hpos x hx, fun y hy ↦ hxmin hy⟩
