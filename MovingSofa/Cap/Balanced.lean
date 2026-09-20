import MovingSofa.Motion.Basic
import MovingSofa.Cap.Area
import MovingSofa.Polygon.AngleSet
import Mathlib.Topology.MetricSpace.HausdorffDistance

noncomputable section

open Filter
open scoped Topology

namespace MovingSofa

def polygonAreaFunctional (Θ : AngleSet) (K : CapSpace Θ.angle) : ℝ :=
  ClassicalResults.area (angleCap Θ K) - ClassicalResults.area (polygonNiche Θ K)

def IsMaximumPolygonCap (Θ : AngleSet) (K : PolygonCapSpace Θ) : Prop :=
  (stripParallelogram Θ.angle).2.2 ∈ (K.val.val : Set Point) ∧
    ∀ L : PolygonCapSpace Θ, polygonAreaFunctional Θ L.val ≤ polygonAreaFunctional Θ K.val

def IsBalancedMaximumCap {ω : ℝ} (K : CapSpace ω) : Prop :=
  ∃ (n : ℕ → ℕ) (hn : ∀ i, 2 ≤ n i), StrictMono n ∧
    (∀ i, ∃ k : ℕ, n i = 2 ^ k) ∧
    ∃ P : ∀ i, PolygonCapSpace (uniformAngleSet ω K.property.1 K.property.2.1 (n i) (hn i)),
      (∀ i, IsMaximumPolygonCap _ (P i)) ∧
      Tendsto (fun i ↦ Metric.hausdorffDist ((P i).val.val : Set Point) (K.val : Set Point))
        atTop (𝓝 0)

end MovingSofa
