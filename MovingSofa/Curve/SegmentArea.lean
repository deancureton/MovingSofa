import MovingSofa.Analysis.MeasureProducts

noncomputable section

namespace MovingSofa

def segmentArea (p q : Point) : ℝ := planeCrossProduct p q / 2

/-- The signed segment area is antisymmetric in its two endpoints. -/
theorem segmentArea_swap (p q : Point) : segmentArea p q = -segmentArea q p := by
  rw [segmentArea, segmentArea, planeCrossProduct_swap p q]
  ring

/-- Translating both endpoints of a segment shifts its signed area by a boundary term. -/
theorem segmentArea_add_right (p q v : Point) :
    segmentArea (p + v) (q + v) =
      segmentArea p q + (v 0 * (q 1 - p 1) - v 1 * (q 0 - p 0)) / 2 := by
  have hadd : ∀ (x y : Point) (i : Fin 2), (x + y) i = x i + y i := fun _ _ _ ↦ by simp
  simp only [segmentArea, planeCrossProduct, hadd]
  ring

/-- The signed area of the segment joining two convex combinations of endpoints is the same
combination of the two signed areas, provided the two endpoints of each pair have a common height:
the mixed terms then cancel. -/
theorem segmentArea_combination_of_apply_one_eq (c : ℝ) {p₁ p₂ q₁ q₂ : Point}
    (hp : p₁ 1 = p₂ 1) (hq : q₁ 1 = q₂ 1) :
    segmentArea ((1 - c) • p₁ + c • p₂) ((1 - c) • q₁ + c • q₂) =
      (1 - c) * segmentArea p₁ q₁ + c * segmentArea p₂ q₂ := by
  simp only [segmentArea, planeCrossProduct, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, hp, hq]
  ring

/-- Two points on a normal line through the origin span no signed area. -/
theorem segmentArea_eq_zero_of_inner_normalVector_eq_zero {p q : Point} {t : ℝ}
    (hp : inner ℝ p (normalVector (t : Real.Angle)) = 0)
    (hq : inner ℝ q (normalVector (t : Real.Angle)) = 0) : segmentArea p q = 0 := by
  rw [segmentArea, planeCrossProduct_eq_inner_frame p q t, hp, hq]
  ring

/-- Collinear additivity of the signed segment area on a common normal line. -/
theorem segmentArea_sub_segmentArea_of_inner_normalVector_eq {p q s : Point} {t c : ℝ}
    (hp : inner ℝ p (normalVector (t : Real.Angle)) = c)
    (hq : inner ℝ q (normalVector (t : Real.Angle)) = c)
    (hs : inner ℝ s (normalVector (t : Real.Angle)) = c) :
    segmentArea p s - segmentArea q s = segmentArea p q := by
  rw [segmentArea, segmentArea, segmentArea, planeCrossProduct_eq_inner_frame p s t,
    planeCrossProduct_eq_inner_frame q s t, planeCrossProduct_eq_inner_frame p q t,
    hp, hq, hs]
  ring

end MovingSofa
