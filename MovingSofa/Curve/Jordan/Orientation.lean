import MovingSofa.Curve.Jordan.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Connected.Basic

noncomputable section

namespace MovingSofa

def jordanInterior (Γ : Set Point) : Set Point :=
  {p | p ∉ Γ ∧ Bornology.IsBounded (connectedComponentIn Γᶜ p)}

def IsCurveAngleLift {a b : ℝ} (x : Set.Icc a b → Point) (p : Point)
    (θ : Set.Icc a b → ℝ) : Prop :=
  Continuous θ ∧ ∀ t,
    Real.cos (θ t) = (x t - p) 0 / ‖x t - p‖ ∧
    Real.sin (θ t) = (x t - p) 1 / ‖x t - p‖

def curveWinding {a b : ℝ} (hab : a ≤ b) (x : Set.Icc a b → Point) (p : Point) : ℝ := by
  classical
  exact if h : ∃ θ, IsCurveAngleLift x p θ then
    (h.choose ⟨b, hab, le_rfl⟩ - h.choose ⟨a, le_rfl, hab⟩) / (2 * Real.pi)
  else 0

def IsOrientedJordanParametrization {a b : ℝ} (hab : a ≤ b)
    (Γ : Set Point) (counterclockwise : Bool) (x : Set.Icc a b → Point) : Prop :=
  a < b ∧ IsJordanCurve Γ ∧ Continuous x ∧ Set.range x = Γ ∧
    x ⟨a, le_rfl, hab⟩ = x ⟨b, hab, le_rfl⟩ ∧
    Set.InjOn x {t | (t : ℝ) < b} ∧
    ∀ p ∈ jordanInterior Γ, curveWinding hab x p = if counterclockwise then 1 else -1

structure OrientedJordanCurve where
  carrier : Set Point
  isJordan : IsJordanCurve carrier
  counterclockwise : Bool

def jordanCurveOrientation :
    (∀ (a b : ℝ), a ≤ b → (Set.Icc a b → Point) → Point → ℝ) ×
    (∀ (a b : ℝ), a ≤ b → Set Point → Bool → (Set.Icc a b → Point) → Prop) :=
  (fun _ _ hab ↦ curveWinding hab, fun _ _ hab ↦ IsOrientedJordanParametrization hab)

end MovingSofa
