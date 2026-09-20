import Mathlib.Analysis.Convex.Basic
import MovingSofa.ForMathlib.MeasureTheory.RegionBetween

/-!
# Planar trapezoids with horizontal parallel sides
-/

namespace EuclideanSpace

/-- A convex planar set containing the four vertices of a trapezoid whose parallel sides are
the horizontal segments at heights `0` and `1` contains the whole trapezoid. -/
theorem horizontalTrapezoid_subset_of_convex {S : Set (EuclideanSpace ℝ (Fin 2))}
    (hS : Convex ℝ S) {l₀ r₀ l₁ r₁ : ℝ}
    (h₀l : (!₂[l₀, 0] : EuclideanSpace ℝ (Fin 2)) ∈ S)
    (h₀r : (!₂[r₀, 0] : EuclideanSpace ℝ (Fin 2)) ∈ S)
    (h₁l : (!₂[l₁, 1] : EuclideanSpace ℝ (Fin 2)) ∈ S)
    (h₁r : (!₂[r₁, 1] : EuclideanSpace ℝ (Fin 2)) ∈ S) :
    {q : EuclideanSpace ℝ (Fin 2) | q 1 ∈ Set.Icc (0 : ℝ) 1 ∧
        q 0 ∈ Set.Icc ((1 - q 1) * l₀ + q 1 * l₁) ((1 - q 1) * r₀ + q 1 * r₁)} ⊆ S := by
  rintro q ⟨⟨hy0, hy1⟩, hql, hqr⟩
  have hleft : ((1 - q 1) • (!₂[l₀, 0] : EuclideanSpace ℝ (Fin 2)) + q 1 • !₂[l₁, 1]) ∈ S :=
    hS h₀l h₁l (by linarith) hy0 (by ring)
  have hright : ((1 - q 1) • (!₂[r₀, 0] : EuclideanSpace ℝ (Fin 2)) + q 1 • !₂[r₁, 1]) ∈ S :=
    hS h₀r h₁r (by linarith) hy0 (by ring)
  obtain ⟨s, hs0, hs1, hs⟩ : ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧
      q 0 = (1 - s) * ((1 - q 1) * l₀ + q 1 * l₁) + s * ((1 - q 1) * r₀ + q 1 * r₁) := by
    rcases (hql.trans hqr).eq_or_lt with hLR | hLR
    · exact ⟨0, le_rfl, zero_le_one, by rw [sub_zero, one_mul, zero_mul, add_zero]; linarith⟩
    · have hne : (1 - q 1) * r₀ + q 1 * r₁ - ((1 - q 1) * l₀ + q 1 * l₁) ≠ 0 := by linarith
      refine ⟨(q 0 - ((1 - q 1) * l₀ + q 1 * l₁)) /
          ((1 - q 1) * r₀ + q 1 * r₁ - ((1 - q 1) * l₀ + q 1 * l₁)),
        div_nonneg (by linarith) (by linarith), by rw [div_le_one (by linarith)]; linarith, ?_⟩
      field_simp
      ring
  have hcoord : ∀ z w : EuclideanSpace ℝ (Fin 2), z 0 = w 0 → z 1 = w 1 → z = w := by
    intro z w h0 h1
    ext i
    fin_cases i
    · exact h0
    · exact h1
  have heq : q = (1 - s) • ((1 - q 1) • (!₂[l₀, 0] : EuclideanSpace ℝ (Fin 2)) + q 1 • !₂[l₁, 1]) +
      s • ((1 - q 1) • (!₂[r₀, 0] : EuclideanSpace ℝ (Fin 2)) + q 1 • !₂[r₁, 1]) := by
    refine hcoord _ _ ?_ ?_
    · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Matrix.cons_val_zero]
      linear_combination hs
    · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Matrix.cons_val_one,
        Matrix.cons_val_fin_one]
      ring
  rw [heq]
  exact hS hleft hright (by linarith) hs0 (by ring)

/-- The planar area of the trapezoid cut from the horizontal band `y₀ ≤ y ≤ y₁` by the two lines
`x = a + b * y` and `x = c + d * y`: the height of the band times the mean of the lengths of its
two horizontal sides. -/
theorem volume_horizontalTrapezoid_band {y₀ y₁ a b c d : ℝ} (hy : y₀ ≤ y₁)
    (h₀ : a + b * y₀ ≤ c + d * y₀) (h₁ : a + b * y₁ ≤ c + d * y₁) :
    MeasureTheory.volume {q : EuclideanSpace ℝ (Fin 2) | q 1 ∈ Set.Icc y₀ y₁ ∧
        q 0 ∈ Set.Icc (a + b * q 1) (c + d * q 1)} =
      ENNReal.ofReal ((y₁ - y₀) *
        ((c + d * y₀ - (a + b * y₀)) + (c + d * y₁ - (a + b * y₁))) / 2) := by
  have hfc : Continuous fun y : ℝ ↦ a + b * y := by fun_prop
  have hgc : Continuous fun y : ℝ ↦ c + d * y := by fun_prop
  rw [volume_horizontalIcc (f := fun y : ℝ ↦ a + b * y) (g := fun y : ℝ ↦ c + d * y)
    (s := Set.Icc y₀ y₁) hfc.measurable hgc.measurable measurableSet_Icc
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hy).mp (hfc.intervalIntegrable y₀ y₁))
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hy).mp (hgc.intervalIntegrable y₀ y₁))
    (fun y hy' ↦ by
      rcases hy.eq_or_lt with rfl | hylt
      · have : y = y₀ := le_antisymm hy'.2 hy'.1
        rw [this]
        exact h₀
      · have hcoef : (y₁ - y) * (c + d * y₀ - (a + b * y₀)) +
            (y - y₀) * (c + d * y₁ - (a + b * y₁)) =
            (y₁ - y₀) * (c + d * y - (a + b * y)) := by ring
        nlinarith [mul_nonneg (by linarith [hy'.2] : (0 : ℝ) ≤ y₁ - y) (by linarith : (0 : ℝ) ≤
            c + d * y₀ - (a + b * y₀)),
          mul_nonneg (by linarith [hy'.1] : (0 : ℝ) ≤ y - y₀) (by linarith : (0 : ℝ) ≤
            c + d * y₁ - (a + b * y₁))])]
  congr 1
  have hrw : ((fun y : ℝ ↦ c + d * y) - fun y : ℝ ↦ a + b * y) =
      fun y : ℝ ↦ (c - a) + (d - b) * y := by
    funext y
    simp only [Pi.sub_apply]
    ring
  have hii : IntervalIntegrable (fun x : ℝ ↦ (d - b) * x) MeasureTheory.volume y₀ y₁ :=
    (by fun_prop : Continuous fun x : ℝ ↦ (d - b) * x).intervalIntegrable y₀ y₁
  rw [hrw, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hy,
    intervalIntegral.integral_add intervalIntegrable_const hii,
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_id]
  simp only [smul_eq_mul]
  ring

/-- The planar area of a trapezoid whose parallel sides are the horizontal segments
`[l₀, r₀] × {0}` and `[l₁, r₁] × {1}` is the mean of their lengths. -/
theorem volume_horizontalTrapezoid {l₀ r₀ l₁ r₁ : ℝ} (h₀ : l₀ ≤ r₀) (h₁ : l₁ ≤ r₁) :
    MeasureTheory.volume {q : EuclideanSpace ℝ (Fin 2) | q 1 ∈ Set.Icc (0 : ℝ) 1 ∧
        q 0 ∈ Set.Icc ((1 - q 1) * l₀ + q 1 * l₁) ((1 - q 1) * r₀ + q 1 * r₁)} =
      ENNReal.ofReal ((r₀ - l₀ + (r₁ - l₁)) / 2) := by
  have hset : {q : EuclideanSpace ℝ (Fin 2) | q 1 ∈ Set.Icc (0 : ℝ) 1 ∧
        q 0 ∈ Set.Icc ((1 - q 1) * l₀ + q 1 * l₁) ((1 - q 1) * r₀ + q 1 * r₁)} =
      {q : EuclideanSpace ℝ (Fin 2) | q 1 ∈ Set.Icc (0 : ℝ) 1 ∧
        q 0 ∈ Set.Icc (l₀ + (l₁ - l₀) * q 1) (r₀ + (r₁ - r₀) * q 1)} := by
    refine Set.ext fun q ↦ ?_
    simp only [Set.mem_ofPred_eq,
      show (1 - q 1) * l₀ + q 1 * l₁ = l₀ + (l₁ - l₀) * q 1 from by ring,
      show (1 - q 1) * r₀ + q 1 * r₁ = r₀ + (r₁ - r₀) * q 1 from by ring]
  rw [hset, volume_horizontalTrapezoid_band zero_le_one (by simpa using h₀) (by simpa using h₁)]
  congr 1
  ring

end EuclideanSpace
