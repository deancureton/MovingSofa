import GerverSofa.KernelOnly.PartF.F01SetMotion
import GerverSofa.Basic

/-!
# F02: the coordinate homeomorphism

The product `Point = ℝ × ℝ` and `Plane = EuclideanSpace ℝ (Fin 2)`
have the same coordinates and topology. Their norms differ. Accordingly,
the coordinate identification below is a linear equivalence and a
homeomorphism. Euclidean isometries are constructed separately.
-/

noncomputable section

namespace GerverSofa.PartF.Coordinates

def toPlane (q : Point) : Plane := WithLp.toLp 2 ![q.1, q.2]

def fromPlane (q : Plane) : Point := (q 0, q 1)

@[simp] theorem toPlane_zero_coord (q : Point) : toPlane q 0 = q.1 := rfl
@[simp] theorem toPlane_one_coord (q : Point) : toPlane q 1 = q.2 := rfl

theorem plane_ext {q r : Plane} (h0 : q 0 = r 0) (h1 : q 1 = r 1) : q = r := by
  ext i
  fin_cases i
  · exact h0
  · exact h1

@[simp] theorem fromPlane_toPlane (q : Point) : fromPlane (toPlane q) = q := rfl

@[simp] theorem toPlane_fromPlane (q : Plane) : toPlane (fromPlane q) = q := by
  exact plane_ext rfl rfl

theorem toPlane_add (q r : Point) : toPlane (q + r) = toPlane q + toPlane r := by
  exact plane_ext rfl rfl

theorem toPlane_smul (c : ℝ) (q : Point) : toPlane (c • q) = c • toPlane q := by
  exact plane_ext rfl rfl

/-- The coordinate equivalence, without any assertion that the two norms agree. -/
def linearEquiv : Point ≃ₗ[ℝ] Plane where
  toFun := toPlane
  invFun := fromPlane
  left_inv := fromPlane_toPlane
  right_inv := toPlane_fromPlane
  map_add' := toPlane_add
  map_smul' := toPlane_smul

def homeomorph : Point ≃ₜ Plane := linearEquiv.toContinuousLinearEquiv.toHomeomorph

theorem continuous_toPlane : Continuous toPlane :=
  linearEquiv.toContinuousLinearEquiv.continuous

theorem continuous_fromPlane : Continuous fromPlane :=
  linearEquiv.toContinuousLinearEquiv.symm.continuous

theorem image_eq_preimage (S : Set Point) :
    toPlane '' S = fromPlane ⁻¹' S := by
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact hp
  · intro hq
    exact ⟨fromPlane q, hq, toPlane_fromPlane q⟩

theorem isClosed_image {S : Set Point} (hS : IsClosed S) : IsClosed (toPlane '' S) := by
  rw [image_eq_preimage]
  exact hS.preimage continuous_fromPlane

theorem isConnected_image {S : Set Point} (hS : IsConnected S) :
    IsConnected (toPlane '' S) :=
  hS.image toPlane continuous_toPlane.continuousOn

theorem horizontal_image : toPlane '' horizontalArm = Model.horizontalHallway := by
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact hp
  · intro hq
    exact ⟨fromPlane q, hq, toPlane_fromPlane q⟩

theorem vertical_image : toPlane '' verticalArm = Model.verticalHallway := by
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact hp
  · intro hq
    exact ⟨fromPlane q, hq, toPlane_fromPlane q⟩

theorem hallway_image : toPlane '' GerverSofa.hallway = Model.hallway := by
  simp only [GerverSofa.hallway, Model.hallway, Set.image_union,
    horizontal_image, vertical_image]

end GerverSofa.PartF.Coordinates
