import MovingSofa.Curve.Jordan.Interior
import MovingSofa.Curve.PositiveGraphOrientation
import MovingSofa.Geometry.Subgraph

/-!
# The region enclosed by the counterclockwise loop around a positive graph

`MovingSofa.positiveGraphLoop_counterclockwise` identifies the bounded complementary component
of the loop around the graph of a positive `f` with the open subgraph of `f`.  This file records
the resulting description of the closed subgraph: the loop traces exactly the frontier of either
region, and the closed subgraph is the open one together with that frontier.
-/

noncomputable section

namespace MovingSofa

variable {a b : ℝ} {f : ℝ → ℝ} (hab : a < b) (hf : ContinuousOn f (Set.Icc a b))
  (ha : f a = 0) (hb : f b = 0) (hpos : ∀ x ∈ Set.Ioo a b, 0 < f x)

include hab hf ha hb hpos

/-- The bounded complementary component of the positive-graph loop is the open subgraph. -/
theorem jordanInterior_range_positiveGraphLoop :
    jordanInterior (Set.range (positiveGraphLoop a b f)) = openSubgraph a b f :=
  (positiveGraphLoop_counterclockwise a b hab f hf ha hb hpos).2

/-- The positive-graph loop traces the frontier of the open subgraph. -/
theorem frontier_openSubgraph :
    frontier (openSubgraph a b f) = Set.range (positiveGraphLoop a b f) := by
  rw [← jordanInterior_range_positiveGraphLoop hab hf ha hb hpos]
  exact (positiveGraphLoop_counterclockwise a b hab f hf ha hb
    hpos).1.2.1.frontier_jordanInterior

/-- The part of the closed subgraph outside the open one is exactly the loop. -/
theorem closedSubgraph_sdiff_openSubgraph :
    closedSubgraph a b f \ openSubgraph a b f = Set.range (positiveGraphLoop a b f) := by
  rw [← frontier_openSubgraph hab hf ha hb hpos, frontier, (isOpen_openSubgraph hf).interior_eq,
    closure_openSubgraph hab hf ha hb hpos]

/-- The closed subgraph is the open subgraph together with the loop. -/
theorem closedSubgraph_eq_openSubgraph_union_range :
    closedSubgraph a b f = openSubgraph a b f ∪ Set.range (positiveGraphLoop a b f) := by
  rw [← closedSubgraph_sdiff_openSubgraph hab hf ha hb hpos]
  exact (Set.union_sdiff_cancel openSubgraph_subset_closedSubgraph).symm

/-- The positive-graph loop also traces the frontier of the closed subgraph. -/
theorem frontier_closedSubgraph :
    frontier (closedSubgraph a b f) = Set.range (positiveGraphLoop a b f) := by
  rw [frontier, (isClosed_closedSubgraph hf).closure_eq, interior_closedSubgraph hf ha hb,
    closedSubgraph_sdiff_openSubgraph hab hf ha hb hpos]

end MovingSofa
