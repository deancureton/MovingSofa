import MovingSofa.Convex.Combination
import MovingSofa.Classical.Area
import MovingSofa.ForMathlib.MeasureTheory.Volume
import LeanPool.Isoperimetric.BrunnMinkowski

noncomputable section

open MeasureTheory Set
open scoped Pointwise unitInterval

namespace MovingSofa

theorem convexBody_area_superlevel (K L : ConvexBody Point)
    (hK : (11 : ℝ) / 5 ≤ ClassicalResults.area (K : Set Point))
    (hL : (11 : ℝ) / 5 ≤ ClassicalResults.area (L : Set Point)) (t : I) :
    (11 : ℝ) / 5 ≤ ClassicalResults.area (convexBodyCombination t K L : Set Point) := by
  let a : ℝ := 1 - (t : ℝ)
  let b : ℝ := t
  let A : Set Point := a • (K : Set Point)
  let B : Set Point := b • (L : Set Point)
  have ha : 0 ≤ a := by dsimp [a]; exact sub_nonneg.mpr t.2.2
  have hb : 0 ≤ b := t.2.1
  have hab : a + b = 1 := by dsimp [a, b]; ring
  have hAcomp : IsCompact A := K.isCompact.smul a
  have hBcomp : IsCompact B := L.isCompact.smul b
  have hABcomp : IsCompact (A + B) := hAcomp.add hBcomp
  have hbm :
      volume A ^ (2 : ℝ)⁻¹ + volume B ^ (2 : ℝ)⁻¹ ≤
        volume (A + B) ^ (2 : ℝ)⁻¹ := by
    convert brunn_minkowski_euclideanSpace (d := 1) (A := A) (B := B)
      (K.nonempty.smul_set (a := a)) hAcomp.measurableSet
      (L.nonempty.smul_set (a := b)) hBcomp.measurableSet hABcomp.measurableSet using 1 <;>
      norm_num
  have hKfin : volume (K : Set Point) ≠ ⊤ := K.isCompact.measure_lt_top.ne
  have hLfin : volume (L : Set Point) ≠ ⊤ := L.isCompact.measure_lt_top.ne
  have hABfin : volume (A + B) ≠ ⊤ := hABcomp.measure_lt_top.ne
  have hKvol : ENNReal.ofReal ((11 : ℝ) / 5) ≤ volume (K : Set Point) :=
    (ENNReal.ofReal_le_iff_le_toReal hKfin).2 hK
  have hLvol : ENNReal.ofReal ((11 : ℝ) / 5) ≤ volume (L : Set Point) :=
    (ENNReal.ofReal_le_iff_le_toReal hLfin).2 hL
  have hKroot := ENNReal.monotone_rpow_of_nonneg (by positivity : 0 ≤ (2 : ℝ)⁻¹) hKvol
  have hLroot := ENNReal.monotone_rpow_of_nonneg (by positivity : 0 ≤ (2 : ℝ)⁻¹) hLvol
  have hroot :
      ENNReal.ofReal ((11 : ℝ) / 5) ^ (2 : ℝ)⁻¹ ≤
        volume (A + B) ^ (2 : ℝ)⁻¹ := by
    rw [volume_smul_rpow_half (K : Set Point) a ha,
      volume_smul_rpow_half (L : Set Point) b hb] at hbm
    calc
      _ = (ENNReal.ofReal a + ENNReal.ofReal b) *
          ENNReal.ofReal ((11 : ℝ) / 5) ^ (2 : ℝ)⁻¹ := by
        rw [← ENNReal.ofReal_add ha hb, hab, ENNReal.ofReal_one, one_mul]
      _ ≤ ENNReal.ofReal a * volume (K : Set Point) ^ (2 : ℝ)⁻¹ +
          ENNReal.ofReal b * volume (L : Set Point) ^ (2 : ℝ)⁻¹ := by
        rw [add_mul]
        exact add_le_add
          (by simpa [mul_comm] using mul_le_mul_left hKroot (ENNReal.ofReal a))
          (by simpa [mul_comm] using mul_le_mul_left hLroot (ENNReal.ofReal b))
      _ ≤ _ := hbm
  have hvol : ENNReal.ofReal ((11 : ℝ) / 5) ≤ volume (A + B) := by
    calc
      _ = (ENNReal.ofReal ((11 : ℝ) / 5) ^ (2 : ℝ)⁻¹) ^ (2 : ℕ) :=
        (ENNReal.rpow_inv_natCast_pow (by norm_num) _).symm
      _ ≤ (volume (A + B) ^ (2 : ℝ)⁻¹) ^ (2 : ℕ) := pow_le_pow_left' hroot 2
      _ = _ := ENNReal.rpow_inv_natCast_pow (by norm_num) _
  have hcomb : (convexBodyCombination t K L : Set Point) = A + B := by
    rfl
  rw [hcomb]
  exact (ENNReal.ofReal_le_iff_le_toReal hABfin).1 hvol

end MovingSofa
