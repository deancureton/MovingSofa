import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum

/-!
# Exact rational intervals

This module is intentionally small.  It provides the decidable relations used
to audit the published output manifest.  It does not assert that a particular
transcendental expression is enclosed; that analytic soundness is a distinct
proof obligation.
-/

namespace GerverSofa

structure RatInterval where
  lo : ℚ
  hi : ℚ
  deriving Repr, DecidableEq

namespace RatInterval

/-- Strict inclusion in the interior of another interval. -/
def strictInsideB (x outer : RatInterval) : Bool :=
  decide (outer.lo < x.lo ∧ x.hi < outer.hi)

/-- Point interval. -/
def point (x : ℚ) : RatInterval := ⟨x, x⟩

/-- Exact interval addition. -/
def add (x y : RatInterval) : RatInterval :=
  ⟨x.lo + y.lo, x.hi + y.hi⟩

/-- Exact interval negation. -/
def neg (x : RatInterval) : RatInterval :=
  ⟨-x.hi, -x.lo⟩

/-- Exact interval subtraction. -/
def sub (x y : RatInterval) : RatInterval := add x (neg y)

/-- Product hull of two rational intervals. -/
def mul (x y : RatInterval) : RatInterval :=
  let p₁ := x.lo * y.lo
  let p₂ := x.lo * y.hi
  let p₃ := x.hi * y.lo
  let p₄ := x.hi * y.hi
  ⟨min (min p₁ p₂) (min p₃ p₄), max (max p₁ p₂) (max p₃ p₄)⟩

/-! ## Real semantics -/

/-- Semantic membership of a real number in a rational interval. -/
def Contains (z : RatInterval) (x : ℝ) : Prop :=
  (z.lo : ℝ) ≤ x ∧ x ≤ (z.hi : ℝ)

@[simp] theorem strictInsideB_eq_true_iff (x outer : RatInterval) :
    strictInsideB x outer = true ↔ outer.lo < x.lo ∧ x.hi < outer.hi := by
  simp [strictInsideB]

@[simp] theorem contains_point_iff (q : ℚ) (x : ℝ) :
    Contains (point q) x ↔ x = (q : ℝ) := by
  constructor
  · intro hx
    exact le_antisymm hx.2 hx.1
  · rintro rfl
    exact ⟨le_rfl, le_rfl⟩

/-- Exact interval addition is sound over the reals. -/
theorem contains_add {a b : RatInterval} {x y : ℝ}
    (hx : Contains a x) (hy : Contains b y) :
    Contains (add a b) (x + y) := by
  rcases hx with ⟨hxl, hxu⟩
  rcases hy with ⟨hyl, hyu⟩
  simpa [Contains, add] using
    (And.intro (add_le_add hxl hyl) (add_le_add hxu hyu))

/-- Exact interval negation is sound over the reals. -/
theorem contains_neg {a : RatInterval} {x : ℝ}
    (hx : Contains a x) : Contains (neg a) (-x) := by
  rcases hx with ⟨hxl, hxu⟩
  simpa [Contains, neg] using
    (And.intro (neg_le_neg hxu) (neg_le_neg hxl))

/-- Exact interval subtraction is sound over the reals. -/
theorem contains_sub {a b : RatInterval} {x y : ℝ}
    (hx : Contains a x) (hy : Contains b y) :
    Contains (sub a b) (x - y) := by
  simpa [sub, sub_eq_add_neg] using contains_add hx (contains_neg hy)

/-- Closed interval inclusion transports semantic membership. -/
theorem contains_of_subset
    {x outer : RatInterval} {r : ℝ}
    (hsub : outer.lo ≤ x.lo ∧ x.hi ≤ outer.hi)
    (hr : Contains x r) : Contains outer r := by
  constructor
  · exact le_trans (by exact_mod_cast hsub.1) hr.1
  · exact le_trans hr.2 (by exact_mod_cast hsub.2)

/-! ## Multiplicative soundness -/

private theorem min_mul_le_mul_right
    {l u z c : ℝ} (hz : l ≤ z ∧ z ≤ u) :
    min (l * c) (u * c) ≤ z * c := by
  by_cases hc : 0 ≤ c
  · exact le_trans (min_le_left _ _)
      (mul_le_mul_of_nonneg_right hz.1 hc)
  · have hc' : c ≤ 0 := le_of_lt (lt_of_not_ge hc)
    exact le_trans (min_le_right _ _)
      (mul_le_mul_of_nonpos_right hz.2 hc')

private theorem mul_le_max_mul_right
    {l u z c : ℝ} (hz : l ≤ z ∧ z ≤ u) :
    z * c ≤ max (l * c) (u * c) := by
  by_cases hc : 0 ≤ c
  · exact le_trans (mul_le_mul_of_nonneg_right hz.2 hc)
      (le_max_right _ _)
  · have hc' : c ≤ 0 := le_of_lt (lt_of_not_ge hc)
    exact le_trans (mul_le_mul_of_nonpos_right hz.1 hc')
      (le_max_left _ _)

private theorem min_mul_le_mul_left
    {l u z c : ℝ} (hz : l ≤ z ∧ z ≤ u) :
    min (c * l) (c * u) ≤ c * z := by
  by_cases hc : 0 ≤ c
  · exact le_trans (min_le_left _ _)
      (mul_le_mul_of_nonneg_left hz.1 hc)
  · have hc' : c ≤ 0 := le_of_lt (lt_of_not_ge hc)
    exact le_trans (min_le_right _ _)
      (mul_le_mul_of_nonpos_left hz.2 hc')

private theorem mul_le_max_mul_left
    {l u z c : ℝ} (hz : l ≤ z ∧ z ≤ u) :
    c * z ≤ max (c * l) (c * u) := by
  by_cases hc : 0 ≤ c
  · exact le_trans (mul_le_mul_of_nonneg_left hz.2 hc)
      (le_max_right _ _)
  · have hc' : c ≤ 0 := le_of_lt (lt_of_not_ge hc)
    exact le_trans (mul_le_mul_of_nonpos_left hz.1 hc')
      (le_max_left _ _)

/-- The four-corner product hull contains every real product of members. -/
theorem contains_mul {a b : RatInterval} {x y : ℝ}
    (hx : Contains a x) (hy : Contains b y) :
    Contains (mul a b) (x * y) := by
  let A : ℝ := a.lo
  let B : ℝ := a.hi
  let C : ℝ := b.lo
  let D : ℝ := b.hi
  have hx' : A ≤ x ∧ x ≤ B := by
    simpa [A, B, Contains] using hx
  have hy' : C ≤ y ∧ y ≤ D := by
    simpa [C, D, Contains] using hy
  have hLowC :
      min (min (A * C) (A * D)) (min (B * C) (B * D)) ≤
        min (A * C) (B * C) := by
    apply le_min
    · exact le_trans (min_le_left _ _) (min_le_left _ _)
    · exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hLowD :
      min (min (A * C) (A * D)) (min (B * C) (B * D)) ≤
        min (A * D) (B * D) := by
    apply le_min
    · exact le_trans (min_le_left _ _) (min_le_right _ _)
    · exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hLower :
      min (min (A * C) (A * D)) (min (B * C) (B * D)) ≤ x * y := by
    have hXC :
        min (min (A * C) (A * D)) (min (B * C) (B * D)) ≤ x * C :=
      le_trans hLowC (min_mul_le_mul_right hx')
    have hXD :
        min (min (A * C) (A * D)) (min (B * C) (B * D)) ≤ x * D :=
      le_trans hLowD (min_mul_le_mul_right hx')
    exact le_trans (le_min hXC hXD) (min_mul_le_mul_left hy')
  have hUpC :
      max (A * C) (B * C) ≤
        max (max (A * C) (A * D)) (max (B * C) (B * D)) := by
    apply max_le
    · exact le_trans (le_max_left _ _) (le_max_left _ _)
    · exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hUpD :
      max (A * D) (B * D) ≤
        max (max (A * C) (A * D)) (max (B * C) (B * D)) := by
    apply max_le
    · exact le_trans (le_max_right _ _) (le_max_left _ _)
    · exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hUpper :
      x * y ≤ max (max (A * C) (A * D)) (max (B * C) (B * D)) := by
    have hXC : x * C ≤
        max (max (A * C) (A * D)) (max (B * C) (B * D)) :=
      le_trans (mul_le_max_mul_right hx') hUpC
    have hXD : x * D ≤
        max (max (A * C) (A * D)) (max (B * C) (B * D)) :=
      le_trans (mul_le_max_mul_right hx') hUpD
    exact le_trans (mul_le_max_mul_left hy') (max_le hXC hXD)
  simpa [Contains, mul, A, B, C, D] using And.intro hLower hUpper

/-- Rational scaling is a special case of sound interval multiplication. -/
theorem contains_scale {a : ℚ} {z : RatInterval} {x : ℝ}
    (hx : Contains z x) :
    Contains (mul (point a) z) ((a : ℝ) * x) := by
  exact contains_mul ((contains_point_iff a (a : ℝ)).2 rfl) hx

/-- Semantic validity follows from the existence of a contained real point. -/
theorem valid_of_contains {z : RatInterval} {x : ℝ} (hx : Contains z x) :
    (z.lo : ℝ) ≤ (z.hi : ℝ) := le_trans hx.1 hx.2

/-- A strict Boolean inclusion is, in particular, a closed semantic inclusion. -/
theorem contains_of_strictInsideB
    {x outer : RatInterval} {r : ℝ}
    (hstrict : strictInsideB x outer = true)
    (hr : Contains x r) : Contains outer r := by
  have h := (strictInsideB_eq_true_iff x outer).1 hstrict
  exact contains_of_subset
    ⟨le_of_lt h.1, le_of_lt h.2⟩ hr

end RatInterval
end GerverSofa
