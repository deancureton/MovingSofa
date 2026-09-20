import MovingSofa.Geometry.Basic
import MovingSofa.Canonical.Definitions

noncomputable section

namespace MovingSofa

/-- Counterclockwise rotation about the origin. -/
def rotationMap (t : Real.Angle) (p : Point) : Point :=
  (EuclideanGeometry.o.rotation t) p

/-- The horizontal, vertical and rotated vertical strips. -/
def strips (ω : ℝ) : Set Point × Set Point × Set Point :=
  let H : Set Point := {p | 0 ≤ p 1 ∧ p 1 ≤ 1}
  let V : Set Point := {p | 0 ≤ p 0 ∧ p 0 ≤ 1}
  (H, V, rotationMap (ω : Real.Angle) '' V)

/-- The intersection of strips and its two distinguished points. -/
def stripParallelogram (ω : ℝ) : Set Point × Point × Point :=
  ((strips ω).1 ∩ (strips ω).2.2, 0, !₂[Real.tan (Real.pi / 4 - ω / 2), 1])

/-- Corners, walls, rays and quadrants of a hallway. -/
structure HallwayParts where
  innerCorner : Point
  outerCorner : Point
  a : Set Point
  b : Set Point
  c : Set Point
  d : Set Point
  bRay : Set Point
  dRay : Set Point
  outerQuadrant : Set Point
  innerQuadrant : Set Point

/-- The named parts of the fixed hallway. -/
def hallwayParts : HallwayParts where
  innerCorner := 0
  outerCorner := !₂[1, 1]
  a := {p | p 0 = 1}
  b := {p | p 0 = 0}
  c := {p | p 1 = 1}
  d := {p | p 1 = 0}
  bRay := {p | p 0 = 0 ∧ p 1 ≤ 0}
  dRay := {p | p 0 ≤ 0 ∧ p 1 = 0}
  outerQuadrant := {p | p 0 ≤ 1 ∧ p 1 ≤ 1}
  innerQuadrant := {p | p 0 < 0 ∧ p 1 < 0}

/-- Rotation followed by the support-determined translation. -/
def supportingPlacement (s : Set Point) (t : Real.Angle) (p : Point) : Point :=
  rotationMap t p + (supportValue s t - 1) • normalVector t +
    (supportValue s (t + ((Real.pi / 2 : ℝ) : Real.Angle)) - 1) • tangentVector t

/-- The supporting hallway of a nonempty compact set. -/
def supportingHallway (s : Set Point) (t : Real.Angle) : Set Point :=
  supportingPlacement s t '' hallway

/-- The images of all named hallway parts under its supporting placement. -/
def rotatingHallwayParts (s : Set Point) (t : Real.Angle) : HallwayParts where
  innerCorner := supportingPlacement s t hallwayParts.innerCorner
  outerCorner := supportingPlacement s t hallwayParts.outerCorner
  a := supportingPlacement s t '' hallwayParts.a
  b := supportingPlacement s t '' hallwayParts.b
  c := supportingPlacement s t '' hallwayParts.c
  d := supportingPlacement s t '' hallwayParts.d
  bRay := supportingPlacement s t '' hallwayParts.bRay
  dRay := supportingPlacement s t '' hallwayParts.dRay
  outerQuadrant := supportingPlacement s t '' hallwayParts.outerQuadrant
  innerQuadrant := supportingPlacement s t '' hallwayParts.innerQuadrant

end MovingSofa
