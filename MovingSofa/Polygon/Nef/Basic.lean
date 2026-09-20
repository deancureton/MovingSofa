import MovingSofa.Polygon.BooleanFunctions
import MovingSofa.Geometry.Basic

noncomputable section

namespace MovingSofa

structure PlanarHalfPlaneData where
  angle : Real.Angle
  height : ℝ
  upper : Bool
  strict : Bool

def PlanarHalfPlaneData.carrier (H : PlanarHalfPlaneData) : Set Point :=
  normalHalfPlane H.angle H.height H.upper H.strict

def PlanarHalfPlaneData.boundaryLine (H : PlanarHalfPlaneData) : Set Point :=
  normalLine H.angle H.height

def booleanSet {n : ℕ} (E : BooleanFunction n) (H : Fin n → Set Point) : Set Point := by
  classical
  exact {p | E (fun i ↦ decide (p ∈ H i)) = true}

def IsNefPolygon (X : Set Point) : Prop :=
  ∃ (n : ℕ) (E : BooleanFunction n) (H : Fin n → PlanarHalfPlaneData),
    X = booleanSet E (fun i ↦ (H i).carrier)

def IsSimpleNefPolygonWith {n : ℕ} (X : Set Point)
    (H : Fin n → PlanarHalfPlaneData) : Prop :=
  Function.Injective (fun i ↦ (H i).boundaryLine) ∧
    ∃ E : BooleanFunction n, IsMonotoneBooleanFunction E ∧
      X = booleanSet E (fun i ↦ (H i).carrier)

end MovingSofa
