import MovingSofa.Cap.Contacts
import MovingSofa.Geometry.HallwaySupport

noncomputable section

open MeasureTheory Set
open scoped Topology

namespace MovingSofa

/-- Express the two positive arm lengths through support and moving-frame coordinates. -/
theorem tangentArmLengths_positive_frame (K : RightAngleCapSpace) (t : ℝ) :
    (tangentArmLengths K t).1.1 =
        supportValue K.val ((t + Real.pi / 2 : ℝ) : Real.Angle) -
          inner ℝ (edgeVertices K.val (t : Real.Angle)).1
            (tangentVector (t : Real.Angle)) ∧
    (tangentArmLengths K t).2.1 =
        inner ℝ (edgeVertices K.val (t : Real.Angle)).1
            (normalVector (t : Real.Angle)) +
          inner ℝ (edgeVertices K.val ((t + Real.pi / 2 : ℝ) : Real.Angle)).1
            (tangentVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) := by
  have hnn := inner_normalVector_self t
  have htt := inner_tangentVector_self t
  have hnt := inner_normalVector_tangentVector t
  have htn : inner ℝ (tangentVector (t : Real.Angle))
      (normalVector (t : Real.Angle)) = 0 := by
    rw [real_inner_comm, hnt]
  have hA := (edgeVertices_fst_mem K.val (t : Real.Angle)).2
  simp only [tangentArmLengths, capVertices, outerCorner_eq_support_sum,
    inner_sub_left, inner_add_left, real_inner_smul_left, hnn, htt, hnt, htn]
  rw [hA, tangentVector_add_pi_div_two]
  simp [real_inner_comm]
  ring

end MovingSofa
