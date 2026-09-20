import Mathlib

/-!
# F01: the affine-order bridge for issue #5270

The two constructors are deliberately given different names. No upstream
definition is changed or imported, and no theorem from the conjecture file
is used. Both application conventions and the conversion between them are
proved for an arbitrary linear isometry equivalence.
-/

noncomputable section

namespace GerverSofa.PartF

abbrev Plane := EuclideanSpace ℝ (Fin 2)
abbrev Rigid := Plane ≃ᵃⁱ[ℝ] Plane

/-- The ordered coordinate-basis orientation used by the pinned upstream
`FormalConjecturesForMathlib/Geometry/2d.lean`. Importing `Mathlib` alone
does not install that project's plane-orientation instance. -/
instance planeOriented : Module.Oriented ℝ Plane (Fin 2) :=
  ⟨Module.Basis.orientation <| PiLp.basisFun 2 _ _⟩

/-- The second instance supplied by the same upstream plane helper. -/
instance planeFactFinrank : Fact (Module.finrank ℝ Plane = 2) :=
  ⟨finrank_euclideanSpace_fin⟩

/-- The topology used by the pinned `MovingSofa.IsMovingSofa` definition. -/
instance rigidTopology : TopologicalSpace Rigid :=
  .induced (fun e => e.toAffineIsometry.toContinuousAffineMap) inferInstance

/-- The composition currently implemented upstream: `q ↦ R q + p`. -/
def rotateThenTranslate (R : Plane ≃ₗᵢ[ℝ] Plane) (p : Plane) : Rigid :=
  R.toAffineIsometryEquiv.trans (AffineIsometryEquiv.vaddConst ℝ p)

/-- The documented composition: `q ↦ R (q + p)`. -/
def translateThenRotate (R : Plane ≃ₗᵢ[ℝ] Plane) (p : Plane) : Rigid :=
  (AffineIsometryEquiv.vaddConst ℝ p).trans R.toAffineIsometryEquiv

@[simp] theorem rotateThenTranslate_apply
    (R : Plane ≃ₗᵢ[ℝ] Plane) (p q : Plane) :
    rotateThenTranslate R p q = R q + p := rfl

@[simp] theorem translateThenRotate_apply
    (R : Plane ≃ₗᵢ[ℝ] Plane) (p q : Plane) :
    translateThenRotate R p q = R (q + p) := rfl

/-- Keeping the old composition is equivalent to rotating the translation. -/
theorem translateThenRotate_eq_rotateThenTranslate
    (R : Plane ≃ₗᵢ[ℝ] Plane) (p : Plane) :
    translateThenRotate R p = rotateThenTranslate R (R p) := by
  ext q
  simp only [translateThenRotate_apply, rotateThenTranslate_apply, map_add]

def rotation (t : ℝ) : Plane ≃ₗᵢ[ℝ] Plane :=
  EuclideanGeometry.o.rotation (t : Real.Angle)

def bodyFrame (t : ℝ) (p : Plane) : Rigid :=
  translateThenRotate (rotation t) p

def worldFrame (t : ℝ) (x : Plane) : Rigid :=
  rotateThenTranslate (rotation t) x

theorem bodyFrame_eq_worldFrame (t : ℝ) (p : Plane) :
    bodyFrame t p = worldFrame t (rotation t p) :=
  translateThenRotate_eq_rotateThenTranslate (rotation t) p

end GerverSofa.PartF
