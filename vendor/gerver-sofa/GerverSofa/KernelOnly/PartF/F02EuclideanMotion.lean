import GerverSofa.KernelOnly.PartF.F02Coordinates
import GerverSofa.KernelOnly.PartF.F01ExistingMotion

/-!
# F02: the certified sofa as a set with Euclidean rigid motion

Every existing `SE2` action is realized by an affine isometry of `Plane`.
Norm preservation is proved in `Plane` from the equation `c*c+s*s=1`.
Continuity is proved in the induced continuous-affine-map topology of F01.
The final theorem transfers all seven motion fields for the already
certified set, without adding geometric hypotheses.

This module does not identify the set with the literal upstream integral
definition. Its rotation matrices are explicit; their comparison with
`F01.rotation` and the integral representation are separate bridge steps.
-/

noncomputable section
open scoped unitInterval
set_option maxHeartbeats 800000

namespace GerverSofa.PartF.EuclideanMotion

open Coordinates

/-- The standard rotation matrix associated with an existing `SE2` value. -/
def linearPart (g : SE2) : Plane ≃ₗ[ℝ] Plane where
  toFun := fun q => toPlane (g.c * q 0 - g.s * q 1, g.s * q 0 + g.c * q 1)
  invFun := fun q => toPlane (g.c * q 0 + g.s * q 1, -g.s * q 0 + g.c * q 1)
  left_inv := by
    intro q
    apply plane_ext
    · change g.c * (g.c * q 0 - g.s * q 1) +
        g.s * (g.s * q 0 + g.c * q 1) = q 0
      linear_combination (q 0) * g.unit
    · change -g.s * (g.c * q 0 - g.s * q 1) +
        g.c * (g.s * q 0 + g.c * q 1) = q 1
      linear_combination (q 1) * g.unit
  right_inv := by
    intro q
    apply plane_ext
    · change g.c * (g.c * q 0 + g.s * q 1) -
        g.s * (-g.s * q 0 + g.c * q 1) = q 0
      linear_combination (q 0) * g.unit
    · change g.s * (g.c * q 0 + g.s * q 1) +
        g.c * (-g.s * q 0 + g.c * q 1) = q 1
      linear_combination (q 1) * g.unit
  map_add' := by
    intro q r
    apply plane_ext
    · change g.c * (q 0 + r 0) - g.s * (q 1 + r 1) =
        (g.c * q 0 - g.s * q 1) + (g.c * r 0 - g.s * r 1)
      ring
    · change g.s * (q 0 + r 0) + g.c * (q 1 + r 1) =
        (g.s * q 0 + g.c * q 1) + (g.s * r 0 + g.c * r 1)
      ring
  map_smul' := by
    intro c q
    apply plane_ext
    · change g.c * (c * q 0) - g.s * (c * q 1) = c * (g.c * q 0 - g.s * q 1)
      ring
    · change g.s * (c * q 0) + g.c * (c * q 1) = c * (g.s * q 0 + g.c * q 1)
      ring

@[simp] theorem linearPart_zero_coord (g : SE2) (q : Plane) :
    linearPart g q 0 = g.c * q 0 - g.s * q 1 := rfl

@[simp] theorem linearPart_one_coord (g : SE2) (q : Plane) :
    linearPart g q 1 = g.s * q 0 + g.c * q 1 := rfl

theorem linearPart_norm_sq (g : SE2) (q : Plane) :
    ‖linearPart g q‖ ^ 2 = ‖q‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp only [Fin.sum_univ_two]
  change (g.c * q 0 - g.s * q 1) ^ 2 + (g.s * q 0 + g.c * q 1) ^ 2 =
    (q 0) ^ 2 + (q 1) ^ 2
  linear_combination ((q 0) ^ 2 + (q 1) ^ 2) * g.unit

theorem linearPart_norm (g : SE2) (q : Plane) : ‖linearPart g q‖ = ‖q‖ :=
  (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (linearPart_norm_sq g q)

def linearIsometry (g : SE2) : Plane ≃ₗᵢ[ℝ] Plane where
  toLinearEquiv := linearPart g
  norm_map' := linearPart_norm g

/-- A genuine Euclidean affine isometry with the original coordinate action. -/
def ofSE2 (g : SE2) : Rigid :=
  rotateThenTranslate (linearIsometry g) (toPlane (g.tx, g.ty))

theorem ofSE2_apply (g : SE2) (q : Plane) :
    ofSE2 g q = toPlane (g.act (fromPlane q)) := by
  exact plane_ext rfl rfl

theorem ofSE2_apply_toPlane (g : SE2) (q : Point) :
    ofSE2 g (toPlane q) = toPlane (g.act q) := by
  rw [ofSE2_apply, fromPlane_toPlane]

theorem ofSE2_one : ofSE2 SE2.one = AffineIsometryEquiv.refl ℝ Plane := by
  apply AffineIsometryEquiv.ext
  intro q
  change ofSE2 SE2.one q = q
  rw [ofSE2_apply, SE2.one_act, toPlane_fromPlane]

theorem image_action (g : SE2) (S : Set Point) :
    ofSE2 g '' (toPlane '' S) = toPlane '' (g.act '' S) := by
  simp only [Set.image_image, Function.comp_def, ofSE2_apply_toPlane]

/-- The coordinate quarter-turn, used to express continuous matrix coefficients. -/
def quarterTurnLinear : Plane →ₗ[ℝ] Plane where
  toFun := fun q => toPlane (-q 1, q 0)
  map_add' := by
    intro q r
    apply plane_ext
    · change -(q 1 + r 1) = -q 1 + -r 1
      ring
    · rfl
  map_smul' := by
    intro c q
    apply plane_ext
    · change -(c * q 1) = c * (-q 1)
      ring
    · rfl

def quarterTurn : Plane →L[ℝ] Plane := quarterTurnLinear.toContinuousLinearMap

/-- Componentwise continuous `SE2` coefficients give continuity in the
actual topology on affine isometry equivalences. -/
theorem continuous_ofSE2 {X : Type*} [TopologicalSpace X]
    (g : X → SE2)
    (hc : Continuous (fun t => (g t).c))
    (hs : Continuous (fun t => (g t).s))
    (htx : Continuous (fun t => (g t).tx))
    (hty : Continuous (fun t => (g t).ty)) :
    Continuous (fun t => ofSE2 (g t)) := by
  let lin : X → (Plane →L[ℝ] Plane) := fun t =>
    (g t).c • ContinuousLinearMap.id ℝ Plane + (g t).s • quarterTurn
  let offset : X → Plane := fun t => toPlane ((g t).tx, (g t).ty)
  let D := ContinuousAffineMap.decompLinearIsometryEquiv ℝ ℝ Plane Plane
  have hlin : Continuous lin :=
    (hc.smul continuous_const).add (hs.smul continuous_const)
  have hoffset : Continuous offset := continuous_toPlane.comp (htx.prodMk hty)
  have hD : Continuous (fun t => D.symm (offset t, lin t)) :=
    D.symm.continuous.comp (hoffset.prodMk hlin)
  apply continuous_induced_rng.mpr
  change Continuous (fun t => (ofSE2 (g t)).toAffineIsometry.toContinuousAffineMap)
  have heq :
      (fun t => (ofSE2 (g t)).toAffineIsometry.toContinuousAffineMap) =
      (fun t => D.symm (offset t, lin t)) := by
    funext t
    apply ContinuousAffineMap.ext
    intro q
    change ofSE2 (g t) q = D.symm (offset t, lin t) q
    dsimp only [D]
    rw [ContinuousAffineMap.decompLinearIsometryEquiv_symm_apply, ofSE2_apply]
    apply plane_ext
    · change (g t).c * q 0 - (g t).s * q 1 + (g t).tx =
        (g t).c * q 0 + (g t).s * (-q 1) + (g t).tx
      ring
    · change (g t).s * q 0 + (g t).c * q 1 + (g t).ty =
        (g t).c * q 1 + (g t).s * q 0 + (g t).ty
      ring
  rw [heq]
  exact hD

theorem continuous_ofSE2_path (g : ℝ → SE2) (hg : SE2.ContinuousPath g) :
    Continuous (fun t => ofSE2 (g t)) := by
  rcases hg with ⟨hc, hs, htx, hty⟩
  exact continuous_ofSE2 g hc hs htx hty

def sofa : Set Plane := toPlane '' PartC.G

def motion (s : I) : Rigid := ofSE2 (Existing.motion (s : ℝ))

theorem motion_continuous : Continuous motion :=
  (continuous_ofSE2_path Existing.motion Existing.motion_continuous).comp continuous_subtype_val

/-- All seven motion requirements hold for the coordinate image of the
already certified Gerver set. No additional geometric assumptions occur. -/
theorem concrete_movingSofa : Model.IsMovingSofa sofa motion := by
  refine ⟨?_, ?_, motion_continuous, ?_, ?_, ?_, ?_⟩
  · exact isConnected_image PartC.Stage4.globalGeometryCertificate.connected
  · exact isClosed_image PartC.closed_G
  · change ofSE2 (Existing.motion 0) = AffineIsometryEquiv.refl ℝ Plane
    rw [Existing.motion_zero, ofSE2_one]
  · change toPlane '' PartC.G ⊆ Model.horizontalHallway
    rw [← horizontal_image]
    exact Set.image_mono Existing.initial
  · intro s
    change ofSE2 (Existing.motion (s : ℝ)) '' (toPlane '' PartC.G) ⊆ Model.hallway
    rw [image_action, ← hallway_image]
    exact Set.image_mono (Existing.all_times (s : ℝ) s.property)
  · change ofSE2 (Existing.motion 1) '' (toPlane '' PartC.G) ⊆ Model.verticalHallway
    rw [image_action, ← vertical_image]
    exact Set.image_mono Existing.final

end GerverSofa.PartF.EuclideanMotion
