import MovingSofa.Cap.Area
import MovingSofa.Geometry.Contacts
import MovingSofa.Geometry.Hallway

noncomputable section

namespace MovingSofa

/-- Width in a normal direction, for geometric use on nonempty compact sets. -/
def directionalWidth (s : Set Point) (t : Real.Angle) : ℝ :=
  supportValue s t + supportValue s (t + ((Real.pi : ℝ) : Real.Angle))

/-- The positive/negative contacts at the two outer supporting walls. -/
def capVertices {ω : ℝ} (K : CapSpace ω) (t : ℝ) : (Point × Point) × (Point × Point) :=
  (edgeVertices K.1 (t : Real.Angle),
    edgeVertices K.1 ((t + Real.pi / 2 : ℝ) : Real.Angle))

/-- The positive/negative right and left tangent arm lengths of a right-angle cap. -/
def tangentArmLengths (K : RightAngleCapSpace) (t : ℝ) : (ℝ × ℝ) × (ℝ × ℝ) :=
  let y := (rotatingHallwayParts (K.1 : Set Point) (t : Real.Angle)).outerCorner
  let v := capVertices K t
  ((inner ℝ (y - v.1.1) (tangentVector (t : Real.Angle)),
    inner ℝ (y - v.1.2) (tangentVector (t : Real.Angle))),
    (inner ℝ (y - v.2.1) (normalVector (t : Real.Angle)),
      inner ℝ (y - v.2.2) (normalVector (t : Real.Angle))))

/-- The open inner quadrant clipped by the fan. -/
def capWedge {ω : ℝ} (K : CapSpace ω) (t : ℝ) : Set Point :=
  capFan ω ∩ (rotatingHallwayParts (K.1 : Set Point) (t : Real.Angle)).innerQuadrant

/-- The two inner-wall intersections with the lower fan boundary lines. -/
def wedgeEndpoints {ω : ℝ} (K : CapSpace ω) (t : ℝ) : Point × Point :=
  (((supportValue K.1 (t : Real.Angle) - 1) / Real.cos t) • normalVector 0,
    ((supportValue K.1 ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1) /
      Real.cos (ω - t)) • tangentVector (ω : Real.Angle))

/-- Signed right and left gaps between the wedge endpoints and bottom cap contacts. -/
def wedgeGaps {ω : ℝ} (K : CapSpace ω) (t : ℝ) : ℝ × ℝ :=
  (inner ℝ ((capVertices K 0).1.2 - (wedgeEndpoints K t).1) (normalVector 0),
    inner ℝ ((capVertices K ω).2.1 - (wedgeEndpoints K t).2)
      (tangentVector (ω : Real.Angle)))

/-- The selected short boundary arc, including only the specified endpoints. -/
def convexBoundaryArc (K : ConvexBody Point) (a b : ℝ) : Set Point :=
  {(edgeVertices K (a : Real.Angle)).1} ∪
    (⋃ t ∈ Set.Ioo a b, exposedEdge K (t : Real.Angle)) ∪
    {(edgeVertices K (b : Real.Angle)).2}

/-- The right wedge gap in support-function coordinates. -/
theorem wedgeGaps_fst_eq_supportValue {ω : ℝ} (K : CapSpace ω) (t : ℝ) :
    (wedgeGaps K t).1 = supportValue K.val (0 : Real.Angle) -
      (supportValue K.val (t : Real.Angle) - 1) / Real.cos t := by
  have hA := (edgeVertices_snd_mem K.val (0 : Real.Angle)).2
  change inner ℝ (capVertices K 0).1.2 (normalVector (0 : Real.Angle)) =
    supportValue K.val (0 : Real.Angle) at hA
  simp only [wedgeGaps, wedgeEndpoints, inner_sub_left, real_inner_smul_left, hA]
  have hu0 : inner ℝ (normalVector (0 : Real.Angle))
      (normalVector (0 : Real.Angle)) = 1 := by
    rw [← Real.Angle.coe_zero]
    exact inner_normalVector_self 0
  rw [hu0]
  ring

/-- The left wedge gap in support-function coordinates. -/
theorem wedgeGaps_snd_eq_supportValue {ω : ℝ} (K : CapSpace ω)
    (t : ℝ) :
    (wedgeGaps K t).2 =
      supportValue K.val ((ω + Real.pi / 2 : ℝ) : Real.Angle) -
        (supportValue K.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1) /
          Real.cos (ω - t) := by
  have hC := (edgeVertices_fst_mem K.val
    ((ω + Real.pi / 2 : ℝ) : Real.Angle)).2
  change inner ℝ (capVertices K ω).2.1
      (normalVector ((ω + Real.pi / 2 : ℝ) : Real.Angle)) =
    supportValue K.val ((ω + Real.pi / 2 : ℝ) : Real.Angle) at hC
  simp [normalVector, frame, Real.Angle.cos_add_pi_div_two,
    Real.Angle.sin_add_pi_div_two] at hC
  change inner ℝ (capVertices K ω).2.1 (tangentVector (ω : Real.Angle)) =
    supportValue K.val ((ω + Real.pi / 2 : ℝ) : Real.Angle) at hC
  simp only [wedgeGaps, wedgeEndpoints, inner_sub_left,
    real_inner_smul_left, hC]
  rw [inner_tangentVector_self]
  ring

/-- The right wedge endpoint lies on the horizontal axis, at the horizontal intercept of the right
inner wall. -/
theorem wedgeEndpoints_fst_coords {ω : ℝ} (K : CapSpace ω) (t : ℝ) :
    (wedgeEndpoints K t).1 0 = (supportValue K.val (t : Real.Angle) - 1) / Real.cos t ∧
      (wedgeEndpoints K t).1 1 = 0 := by
  constructor <;> simp [wedgeEndpoints, normalVector, frame]

/-- For a right-angle cap the left wedge endpoint also lies on the horizontal axis, at the
horizontal intercept of the left inner wall. -/
theorem wedgeEndpoints_snd_coords (K : RightAngleCapSpace) (t : ℝ) :
    (wedgeEndpoints K t).2 0 =
        -((supportValue K.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1) / Real.sin t) ∧
      (wedgeEndpoints K t).2 1 = 0 := by
  constructor <;> simp [wedgeEndpoints, tangentVector, frame, Real.cos_pi_div_two_sub]

end MovingSofa
