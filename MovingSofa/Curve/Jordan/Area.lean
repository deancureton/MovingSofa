import MovingSofa.Curve.Area
import MovingSofa.Curve.Jordan.Orientation

noncomputable section

namespace MovingSofa

structure ArcBVParametrization (Γ : OrientedJordanArc) where
  a : ℝ
  b : ℝ
  ordered : a ≤ b
  path : ContinuousBVPaths a b
  injective : Function.Injective path.val
  range_eq : Set.range path.val = Γ.carrier
  start_eq : path.val ⟨a, le_rfl, ordered⟩ = Γ.startPoint
  end_eq : path.val ⟨b, ordered, le_rfl⟩ = Γ.endPoint

structure ClosedBVParametrization (Γ : OrientedJordanCurve) where
  a : ℝ
  b : ℝ
  ordered : a ≤ b
  path : ContinuousBVPaths a b
  oriented : IsOrientedJordanParametrization ordered Γ.carrier Γ.counterclockwise path.val

abbrev RectifiableOrientedArc :=
  {Γ : OrientedJordanArc // Nonempty (ArcBVParametrization Γ)}

abbrev RectifiableOrientedCurve :=
  {Γ : OrientedJordanCurve // Nonempty (ClosedBVParametrization Γ)}

def jordanArcArea (Γ : RectifiableOrientedArc) : ℝ :=
  curveAreaFunctional (Classical.choice Γ.property).path

def jordanClosedCurveArea (Γ : RectifiableOrientedCurve) : ℝ :=
  curveAreaFunctional (Classical.choice Γ.property).path

def jordanArea : (RectifiableOrientedArc → ℝ) × (RectifiableOrientedCurve → ℝ) :=
  (jordanArcArea, jordanClosedCurveArea)

end MovingSofa
