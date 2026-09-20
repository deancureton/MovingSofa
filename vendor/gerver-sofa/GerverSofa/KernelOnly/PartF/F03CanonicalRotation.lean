import GerverSofa.KernelOnly.PartF.F02EuclideanMotion
import GerverSofa.KernelOnly.PartF.F01PhaseAlgebra

/-!
# F03: the upstream-oriented rotation in the certified coordinates

The orientation is the ordered coordinate-basis orientation installed in F01,
with the same definition as the pinned upstream plane helper. We compute its
area form, then its right-angle rotation, before comparing rotation matrices.
No replacement orientation or additional orientation hypothesis is introduced.
-/

noncomputable section
set_option maxHeartbeats 800000

namespace GerverSofa.PartF.CanonicalRotation

open Coordinates EuclideanMotion

/-- The sign is fixed by the ordered orthonormal coordinate basis. -/
theorem areaForm_coordinates (q r : Plane) :
    EuclideanGeometry.o.areaForm q r = q 0 * r 1 - q 1 * r 0 := by
  rw [Orientation.areaForm_to_volumeForm,
    EuclideanGeometry.o.volumeForm_robust (EuclideanSpace.basisFun (Fin 2) ℝ) rfl,
    Module.Basis.det_apply]
  simp [Module.Basis.toMatrix, Matrix.det_fin_two, mul_comm]

/-- The positive quarter-turn is exactly `(x,y) ↦ (-y,x)`. -/
theorem rightAngleRotation_apply (q : Plane) :
    EuclideanGeometry.o.rightAngleRotation q = toPlane (-q 1, q 0) := by
  apply plane_ext
  · have h := EuclideanGeometry.o.inner_rightAngleRotation_left q
      (EuclideanSpace.basisFun (Fin 2) ℝ 0)
    rw [EuclideanSpace.inner_basisFun_real, areaForm_coordinates] at h
    simpa [EuclideanSpace.basisFun_apply, PiLp.single_apply] using h
  · have h := EuclideanGeometry.o.inner_rightAngleRotation_left q
      (EuclideanSpace.basisFun (Fin 2) ℝ 1)
    rw [EuclideanSpace.inner_basisFun_real, areaForm_coordinates] at h
    simpa [EuclideanSpace.basisFun_apply, PiLp.single_apply] using h

theorem rotation_apply (t : ℝ) (q : Plane) :
    rotation t q = toPlane (Romik.rot t (fromPlane q)) := by
  change EuclideanGeometry.o.rotation (t : Real.Angle) q = _
  rw [Orientation.rotation_apply, rightAngleRotation_apply]
  simp only [Real.Angle.cos_coe, Real.Angle.sin_coe]
  apply plane_ext
  · change Real.cos t * q 0 + Real.sin t * (-q 1) =
      Real.cos t * q 0 - Real.sin t * q 1
    ring
  · change Real.cos t * q 1 + Real.sin t * q 0 =
      Real.sin t * q 0 + Real.cos t * q 1
    ring

theorem rotation_toPlane (t : ℝ) (q : Point) :
    rotation t (toPlane q) = toPlane (Romik.rot t q) := by
  rw [rotation_apply, fromPlane_toPlane]

theorem linearIsometry_eq_rotation (g : SE2) (t : ℝ)
    (hc : g.c = Real.cos t) (hs : g.s = Real.sin t) :
    linearIsometry g = rotation t := by
  apply LinearIsometryEquiv.ext
  intro q
  rw [rotation_apply]
  change toPlane (g.c * q 0 - g.s * q 1, g.s * q 0 + g.c * q 1) =
    toPlane (Real.cos t * q 0 - Real.sin t * q 1,
      Real.sin t * q 0 + Real.cos t * q 1)
  rw [hc, hs]

theorem ofSE2_eq_worldFrame (g : SE2) (t : ℝ)
    (hc : g.c = Real.cos t) (hs : g.s = Real.sin t) :
    ofSE2 g = worldFrame t (toPlane (g.tx, g.ty)) := by
  unfold ofSE2 worldFrame
  rw [linearIsometry_eq_rotation g t hc hs]

/-- The physical angle is `s * (π/2)`, including both endpoints. -/
theorem romikFrame_eq_worldFrame (p : Romik.Params) (s : ℝ) :
    ofSE2 (Romik.frame p s) =
      worldFrame (Romik.angle s) (toPlane (Romik.path p (Romik.angle s))) := by
  exact ofSE2_eq_worldFrame (Romik.frame p s) (Romik.angle s) rfl rfl

theorem romikFrame_zero_act (p : Romik.Params)
    (hzero : Romik.path p 0 = (0, 0)) (q : Point) :
    (Romik.frame p 0).act q = q := by
  simp [Romik.frame, Romik.angle, hzero, SE2.act]

/-- The already proved five-phase algebra now uses the canonical rotation. -/
theorem closedPath_rotation (d : Reduced.Params)
    (hd : Reduced.Equations d) (t : ℝ) :
    rotation t (toPlane (Phases.closedPath d t)) =
      toPlane (Romik.path (Phases.dictionary d) t) := by
  rw [rotation_toPlane, Phases.fivePhaseRepresentation d hd t]

end GerverSofa.PartF.CanonicalRotation
