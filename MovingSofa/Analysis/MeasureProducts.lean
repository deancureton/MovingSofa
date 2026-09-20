import MovingSofa.ForMathlib.MeasureTheory.Measure.HaarNullSets
import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import MovingSofa.Geometry.Frame

noncomputable section

open MeasureTheory

namespace MovingSofa

def functionMeasureMul {X : Type*} [MeasurableSpace X]
    (f : X → ℝ) (μ : SignedMeasure X) : SignedMeasure X :=
  μ.withDensity f (ContinuousLinearMap.mul ℝ ℝ)

def pairFunctionMeasureMul {X : Type*} [MeasurableSpace X]
    (f : (X → ℝ) × (X → ℝ)) (μ : SignedMeasure X) :
    SignedMeasure X × SignedMeasure X :=
  (functionMeasureMul f.1 μ, functionMeasureMul f.2 μ)

def functionPairMeasureMul {X : Type*} [MeasurableSpace X]
    (f : X → ℝ) (μ : SignedMeasure X × SignedMeasure X) :
    SignedMeasure X × SignedMeasure X :=
  (functionMeasureMul f μ.1, functionMeasureMul f μ.2)

def functionMeasureDot {X : Type*} [MeasurableSpace X]
    (f : (X → ℝ) × (X → ℝ)) (μ : SignedMeasure X × SignedMeasure X) :
    SignedMeasure X :=
  functionMeasureMul f.1 μ.1 + functionMeasureMul f.2 μ.2

def planeCrossProduct (p q : Point) : ℝ :=
  p 0 * q 1 - p 1 * q 0

def functionMeasureCross {X : Type*} [MeasurableSpace X]
    (f : (X → ℝ) × (X → ℝ)) (μ : SignedMeasure X × SignedMeasure X) :
    SignedMeasure X :=
  functionMeasureMul f.1 μ.2 - functionMeasureMul f.2 μ.1

def functionMeasureProducts (X : Type*) [MeasurableSpace X] :
    ((X → ℝ) → SignedMeasure X → SignedMeasure X) ×
    (((X → ℝ) × (X → ℝ)) → SignedMeasure X → SignedMeasure X × SignedMeasure X) ×
    ((X → ℝ) → (SignedMeasure X × SignedMeasure X) → SignedMeasure X × SignedMeasure X) ×
    (((X → ℝ) × (X → ℝ)) → (SignedMeasure X × SignedMeasure X) → SignedMeasure X) :=
  (functionMeasureMul, pairFunctionMeasureMul, functionPairMeasureMul, functionMeasureDot)

def planeCrossProducts (X : Type*) [MeasurableSpace X] :
    (Point → Point → ℝ) ×
    (((X → ℝ) × (X → ℝ)) → (SignedMeasure X × SignedMeasure X) → SignedMeasure X) :=
  (planeCrossProduct, functionMeasureCross)

/-! ### The oriented planar determinant

Basic algebra of `planeCrossProduct`, the transitivity of the order it induces on the closed
first quadrant, and the two shapes of level set used when a planar region is fanned into
triangles over a base point.
-/

@[simp] theorem planeCrossProduct_self (p : Point) : planeCrossProduct p p = 0 := by
  simp only [planeCrossProduct]
  ring

@[simp] theorem planeCrossProduct_zero_left (p : Point) : planeCrossProduct 0 p = 0 := by
  simp [planeCrossProduct]

@[simp] theorem planeCrossProduct_zero_right (p : Point) : planeCrossProduct p 0 = 0 := by
  simp [planeCrossProduct]

/-- The oriented determinant is antisymmetric. -/
theorem planeCrossProduct_swap (p q : Point) :
    planeCrossProduct p q = -planeCrossProduct q p := by
  simp only [planeCrossProduct]
  ring

/-- The oriented determinant is the inner product against the quarter turn of its first
argument. -/
theorem planeCrossProduct_eq_inner (p q : Point) :
    planeCrossProduct p q = inner ℝ q !₂[-p 1, p 0] := by
  simp [planeCrossProduct, PiLp.inner_apply, Fin.sum_univ_two]
  ring

/-- In the closed first quadrant the oriented determinant order is transitive: if `v` is
nonzero and both `u × v` and `v × w` are nonnegative, then so is `u × w`. -/
theorem planeCrossProduct_nonneg_trans {u v w : Point} (hv : v ≠ 0)
    (hu0 : 0 ≤ u 0) (hu1 : 0 ≤ u 1) (hv0 : 0 ≤ v 0) (hv1 : 0 ≤ v 1)
    (hw0 : 0 ≤ w 0) (hw1 : 0 ≤ w 1)
    (huv : 0 ≤ planeCrossProduct u v) (hvw : 0 ≤ planeCrossProduct v w) :
    0 ≤ planeCrossProduct u w := by
  have hvpos : 0 < v 0 ^ 2 + v 1 ^ 2 := by
    rcases eq_or_lt_of_le (by positivity : (0 : ℝ) ≤ v 0 ^ 2 + v 1 ^ 2) with h | h
    · refine absurd ?_ hv
      have h0 : v 0 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
      have h1 : v 1 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
      ext i
      fin_cases i
      · simpa using h0
      · simpa using h1
    · exact h
  have hid : planeCrossProduct u w * (v 0 ^ 2 + v 1 ^ 2)
      = (w 0 * v 0 + w 1 * v 1) * planeCrossProduct u v
        + planeCrossProduct v w * (u 0 * v 0 + u 1 * v 1) := by
    simp only [planeCrossProduct]
    ring
  nlinarith [mul_nonneg (add_nonneg (mul_nonneg hw0 hv0) (mul_nonneg hw1 hv1)) huv,
    mul_nonneg hvw (add_nonneg (mul_nonneg hu0 hv0) (mul_nonneg hu1 hv1))]

/-- The closed angular sector between two rays through a base point is convex. -/
theorem convex_setOf_planeCrossProduct_fan (u v L : Point) :
    Convex ℝ {x : Point | 0 ≤ planeCrossProduct u (x - L) ∧
      0 ≤ planeCrossProduct (x - L) v} := by
  intro x hx y hy a b ha hb hab
  obtain rfl : b = 1 - a := by linarith
  simp only [Set.mem_ofPred_eq, planeCrossProduct, PiLp.sub_apply, PiLp.add_apply,
    PiLp.smul_apply, smul_eq_mul] at hx hy ⊢
  constructor
  · nlinarith [mul_nonneg ha hx.1, mul_nonneg hb hy.1]
  · nlinarith [mul_nonneg ha hx.2, mul_nonneg hb hy.2]

/-- The line through a base point in a nonzero direction carries no planar area. -/
theorem volume_setOf_planeCrossProduct_sub_eq_zero {w : Point} (hw : w ≠ 0) (L : Point) :
    volume {x : Point | planeCrossProduct w (x - L) = 0} = 0 := by
  have hrot : (!₂[-w 1, w 0] : Point) ≠ 0 := by
    intro h
    refine hw ?_
    have h0 : w 0 = 0 := by simpa using congrArg (fun v : Point ↦ v 1) h
    have h1 : w 1 = 0 := by simpa using congrArg (fun v : Point ↦ v 0) h
    ext i
    fin_cases i
    · simpa using h0
    · simpa using h1
  have hset : {x : Point | planeCrossProduct w (x - L) = 0}
      = {x : Point | inner ℝ x (!₂[-w 1, w 0] : Point) =
          inner ℝ L (!₂[-w 1, w 0] : Point)} := by
    ext x
    simp only [Set.mem_ofPred_eq, planeCrossProduct_eq_inner, inner_sub_left, sub_eq_zero]
  rw [hset]
  exact volume.addHaar_setOf_real_inner_eq hrot _

/-- The planar cross product is the frame determinant at every angle. -/
theorem planeCrossProduct_eq_inner_frame (a b : Point) (t : ℝ) :
    planeCrossProduct a b =
      inner ℝ a (normalVector (t : Real.Angle)) * inner ℝ b (tangentVector (t : Real.Angle)) -
        inner ℝ a (tangentVector (t : Real.Angle)) *
          inner ℝ b (normalVector (t : Real.Angle)) := by
  simp only [planeCrossProduct, normalVector, tangentVector, frame, PiLp.inner_apply,
    Fin.sum_univ_two, Real.Angle.cos_coe, Real.Angle.sin_coe, RCLike.inner_apply,
    conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one]
  linear_combination (a.ofLp 1 * b.ofLp 0 - a.ofLp 0 * b.ofLp 1) * (Real.sin_sq_add_cos_sq t)

/-- The oriented determinant of a point against the frame tangent is its normal coordinate. -/
theorem planeCrossProduct_tangentVector (p : Point) (t : Real.Angle) :
    planeCrossProduct p (tangentVector t) = inner ℝ p (normalVector t) := by
  simp [planeCrossProduct, normalVector, tangentVector, frame, PiLp.inner_apply,
    Fin.sum_univ_two]
  ring

end MovingSofa
