import MovingSofa.Geometry.Contacts
import MovingSofa.Geometry.HallwayParts
import MovingSofa.Convex.Limits

noncomputable section

namespace MovingSofa

theorem outerCorner_eq_support_sum (K : ConvexBody Point) (t : ℝ) :
    (rotatingHallwayParts (K : Set Point) (t : Real.Angle)).outerCorner =
      supportValue K (t : Real.Angle) • normalVector (t : Real.Angle) +
      supportValue K ((t + Real.pi / 2 : ℝ) : Real.Angle) • tangentVector (t : Real.Angle) := by
  have hrot : rotationMap (t : Real.Angle) (!₂[1, 1] : Point) =
      normalVector (t : Real.Angle) + tangentVector (t : Real.Angle) := by
    unfold rotationMap
    rw [Orientation.rotation_apply, rightAngleRotation_apply]
    ext i
    fin_cases i <;> simp [normalVector, tangentVector, frame]
    ring
  simp only [rotatingHallwayParts, supportingPlacement, hallwayParts, hrot, Real.Angle.coe_add]
  module

/-- Two supporting lines at angular difference exactly `π / 2` meet at the outer corner of the
rotating supporting hallway. -/
theorem supportingIntersection_add_pi_div_two_eq_outerCorner (K : ConvexBody Point) (t : ℝ) :
    supportingIntersection K (t : Real.Angle) ((t + Real.pi / 2 : ℝ) : Real.Angle) =
      (rotatingHallwayParts (K : Set Point) (t : Real.Angle)).outerCorner := by
  have hd : ((t + Real.pi / 2 : ℝ) : Real.Angle) - (t : Real.Angle) =
      ((Real.pi / 2 : ℝ) : Real.Angle) := by
    rw [← Real.Angle.coe_sub, show t + Real.pi / 2 - t = Real.pi / 2 from by ring]
  rw [supportingIntersection, hd, Real.Angle.cos_coe, Real.Angle.sin_coe, Real.cos_pi_div_two,
    Real.sin_pi_div_two, outerCorner_eq_support_sum]
  simp only [mul_zero, sub_zero, div_one]

/-- The outer corner of the rotating supporting hallway is its inner corner translated by the
frame sum `u_t + v_t`. -/
theorem outerCorner_eq_innerCorner_add (K : ConvexBody Point) (t : ℝ) :
    (rotatingHallwayParts (K : Set Point) (t : Real.Angle)).outerCorner =
      (rotatingHallwayParts (K : Set Point) (t : Real.Angle)).innerCorner +
        (normalVector (t : Real.Angle) + tangentVector (t : Real.Angle)) := by
  rw [outerCorner_eq_support_sum]
  simp only [rotatingHallwayParts, hallwayParts, supportingPlacement, rotationMap,
    map_zero, zero_add, Real.Angle.coe_add]
  module

theorem continuous_outerCorner (K : ConvexBody Point) :
    Continuous
      (fun s : ℝ ↦ (rotatingHallwayParts (K : Set Point) (s : Real.Angle)).outerCorner) := by
  simp_rw [outerCorner_eq_support_sum]
  exact ((continuous_supportValue_real K).smul continuous_normalVector_real).add
    (((continuous_supportValue_real K).comp (continuous_id.add_const _)).smul
      (continuous_iff_continuousAt.mpr fun t ↦ (hasDerivAt_tangentVector t).continuousAt))

end MovingSofa
