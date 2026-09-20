import MovingSofa.Cap.CornerPaths
import MovingSofa.Convex.ArcArea
import MovingSofa.Cap.Tail.Arcs
import MovingSofa.Cap.Tail.Bodies

noncomputable section

namespace MovingSofa

def upperBoundQ (T : CapTailSpace) : ℝ :=
  ClassicalResults.area (T.cap.val.val : Set Point) +
    convexArcArea T.leftBody (3 * Real.pi / 2)
      (3 * Real.pi / 2 + paperGerverConstants.2.2) +
    segmentArea (rightLeftTailArcs T.rightBody T.leftBody).2.endPoint
      (distinguishedCapSides T.cap.val).2.corner -
    curveAreaFunctional (capMiddleBV T.cap) +
    segmentArea (distinguishedCapSides T.cap.val).1.corner
      (rightLeftTailArcs T.rightBody T.leftBody).1.startPoint +
    convexArcArea T.rightBody (Real.pi + paperGerverConstants.2.1) (3 * Real.pi / 2)

end MovingSofa
