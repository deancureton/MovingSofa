import MovingSofa.Cap.Contacts
import MovingSofa.Gerver.Parameters

noncomputable section

namespace MovingSofa

structure DirectedArcData where
  carrier : Set Point
  startPoint : Point
  endPoint : Point

def rightLeftTailArcs (B D : ConvexBody Point) : DirectedArcData × DirectedArcData :=
  (⟨convexBoundaryArc B (Real.pi + paperGerverConstants.2.1) (3 * Real.pi / 2),
    (edgeVertices B ((Real.pi + paperGerverConstants.2.1 : ℝ) : Real.Angle)).1,
    (edgeVertices B ((3 * Real.pi / 2 : ℝ) : Real.Angle)).2⟩,
   ⟨convexBoundaryArc D (3 * Real.pi / 2) (3 * Real.pi / 2 + paperGerverConstants.2.2),
    (edgeVertices D ((3 * Real.pi / 2 : ℝ) : Real.Angle)).1,
    (edgeVertices D ((3 * Real.pi / 2 + paperGerverConstants.2.2 : ℝ) : Real.Angle)).2⟩)

end MovingSofa
