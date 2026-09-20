import MovingSofa.Geometry.Plane
import Mathlib.Analysis.Convex.Segment

namespace MovingSofa

structure XMonotonePolylineData where
  edges : ℕ
  vertices : Fin (edges + 1) → Point
  increasing : StrictMono (fun i ↦ vertices i 0)

def XMonotonePolylineData.carrier (p : XMonotonePolylineData) : Set Point :=
  ⋃ i : Fin p.edges, segment ℝ (p.vertices i.castSucc) (p.vertices i.succ)

def IsXMonotonePolyline (S : Set Point) : Prop :=
  ∃ p : XMonotonePolylineData, S = p.carrier

end MovingSofa
