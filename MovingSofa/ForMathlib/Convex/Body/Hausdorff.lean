import Mathlib.Analysis.Convex.Body
import Mathlib.Topology.MetricSpace.HausdorffDistance

open Filter
open scoped Topology

namespace ConvexBody

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Eventual membership persists in a Hausdorff limit of convex bodies. -/
theorem mem_of_tendsto_hausdorffDist (q : E) (K : ℕ → ConvexBody E) (L : ConvexBody E)
    (hev : ∀ᶠ n in atTop, q ∈ (K n : Set E))
    (hlim : Tendsto (fun n ↦ Metric.hausdorffDist (K n : Set E) (L : Set E))
      atTop (𝓝 0)) : q ∈ (L : Set E) := by
  have hle : (fun _ : ℕ ↦ Metric.infDist q (L : Set E)) ≤ᶠ[atTop]
      (fun n ↦ Metric.hausdorffDist (K n : Set E) (L : Set E)) := by
    filter_upwards [hev] with n hn
    exact Metric.infDist_le_hausdorffDist_of_mem hn
      (Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded
        (K n).nonempty L.nonempty (K n).isCompact.isBounded L.isCompact.isBounded)
  have hz : Metric.infDist q (L : Set E) ≤ 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hlim hle
  exact (IsClosed.mem_iff_infDist_zero L.isClosed L.nonempty).mpr
    (le_antisymm hz Metric.infDist_nonneg)

end ConvexBody
