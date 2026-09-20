import MovingSofa.ForMathlib.Analysis.InnerProductSpace.Linear
import MovingSofa.Geometry.Plane
import Mathlib.Analysis.Convex.Body
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle

noncomputable section

namespace MovingSofa

/-- The normal and positively oriented tangent at an angular direction. -/
def frame (t : Real.Angle) : Point × Point :=
  (!₂[t.cos, t.sin], !₂[-t.sin, t.cos])

/-- The unit normal of the angular frame. -/
abbrev normalVector (t : Real.Angle) : Point := (frame t).1

/-- The counterclockwise unit tangent of the angular frame. -/
abbrev tangentVector (t : Real.Angle) : Point := (frame t).2

/-- The support value; geometric results require a nonempty compact set. -/
def supportValue (s : Set Point) (t : Real.Angle) : ℝ :=
  sSup ((fun p ↦ inner ℝ p (normalVector t)) '' s)

/-- The line with the given unit normal and signed offset. -/
def normalLine (t : Real.Angle) (h : ℝ) : Set Point :=
  {p | inner ℝ p (normalVector t) = h}

/-- A normal half-plane: `upper` chooses the greater side, `strict` its open version. -/
def normalHalfPlane (t : Real.Angle) (h : ℝ) (upper strict : Bool) : Set Point :=
  {p | if upper then
    if strict then h < inner ℝ p (normalVector t) else h ≤ inner ℝ p (normalVector t)
  else
    if strict then inner ℝ p (normalVector t) < h else inner ℝ p (normalVector t) ≤ h}

/-- Closed normal half-planes are closed, on either side of the boundary line. -/
theorem isClosed_normalHalfPlane (t : Real.Angle) (h : ℝ) (upper : Bool) :
    IsClosed (normalHalfPlane t h upper false) := by
  cases upper
  · exact isClosed_le (continuous_id.inner continuous_const) continuous_const
  · exact isClosed_le continuous_const (continuous_id.inner continuous_const)

/-- Closed normal half-planes are convex, on either side of the boundary line. -/
theorem convex_normalHalfPlane (t : Real.Angle) (h : ℝ) (upper : Bool) :
    Convex ℝ (normalHalfPlane t h upper false) := by
  have hlin : IsLinearMap ℝ fun p : Point ↦ inner ℝ p (normalVector t) :=
    isLinearMap_inner_left _
  cases upper
  · exact convex_halfSpace_le hlin h
  · exact convex_halfSpace_ge hlin h

/-- Open normal half-planes are convex, on either side of the boundary line. -/
theorem convex_normalHalfPlane_open (t : Real.Angle) (h : ℝ) (upper : Bool) :
    Convex ℝ (normalHalfPlane t h upper true) := by
  have hlin : IsLinearMap ℝ fun p : Point ↦ inner ℝ p (normalVector t) :=
    isLinearMap_inner_left _
  cases upper
  · exact convex_halfSpace_lt hlin h
  · exact convex_halfSpace_gt hlin h

/-- The supporting line and closed containing half-plane of a nonempty compact set. -/
def supportingLineHalfPlane (s : Set Point) (t : Real.Angle) : Set Point × Set Point :=
  (normalLine t (supportValue s t), normalHalfPlane t (supportValue s t) false false)

/-- A closed supporting half-plane, read through the opposite normal direction. -/
theorem supportingLineHalfPlane_snd_eq_normalHalfPlane {s : Set Point} {t u : Real.Angle}
    {h : ℝ} (hn : normalVector u = -normalVector t) (hs : supportValue s u = -h) :
    (supportingLineHalfPlane s u).2 = normalHalfPlane t h true false := by
  ext q
  show inner ℝ q (normalVector u) ≤ supportValue s u ↔ h ≤ inner ℝ q (normalVector t)
  rw [hn, inner_neg_right, hs]
  constructor <;> intro hq <;> linarith

end MovingSofa
