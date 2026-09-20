import GerverSofa.KernelOnly.LeanCertNumericsRows.FullImage21

/-!
# Final LeanCert numerical certificate for Gerver

All expensive 22D checks are already cached in a serial dependency chain
ending at `FullImage21`.  This module only assembles them into the global
norm/self-map facts and the unique-root theorem.
-/

noncomputable section

namespace GerverSofa
namespace PartALeanCert

open LeanCert.Core
open LeanCert.Engine

theorem full_bound_lt : intervalMatrixBound fullPJ < qTarget := by
  apply matrixBound_lt_of_rows fullPJ qTarget qTarget_pos
  intro i
  fin_cases i
  · exact full_row_0_lt
  · exact full_row_1_lt
  · exact full_row_2_lt
  · exact full_row_3_lt
  · exact full_row_4_lt
  · exact full_row_5_lt
  · exact full_row_6_lt
  · exact full_row_7_lt
  · exact full_row_8_lt
  · exact full_row_9_lt
  · exact full_row_10_lt
  · exact full_row_11_lt
  · exact full_row_12_lt
  · exact full_row_13_lt
  · exact full_row_14_lt
  · exact full_row_15_lt
  · exact full_row_16_lt
  · exact full_row_17_lt
  · exact full_row_18_lt
  · exact full_row_19_lt
  · exact full_row_20_lt
  · exact full_row_21_lt

theorem full_bound_le : intervalMatrixBound fullPJ ≤ qTarget :=
  full_bound_lt.le

theorem full_point_values_mem :
    ∀ j : Fin 22,
      systemEval fullExpr
          (fun k => ((zeroCenter (n := 22) k : ℚ) : ℝ)) j ∈
        fullPointCache j := by
  intro j
  fin_cases j
  · exact full_point_0_mem
  · exact full_point_1_mem
  · exact full_point_2_mem
  · exact full_point_3_mem
  · exact full_point_4_mem
  · exact full_point_5_mem
  · exact full_point_6_mem
  · exact full_point_7_mem
  · exact full_point_8_mem
  · exact full_point_9_mem
  · exact full_point_10_mem
  · exact full_point_11_mem
  · exact full_point_12_mem
  · exact full_point_13_mem
  · exact full_point_14_mem
  · exact full_point_15_mem
  · exact full_point_16_mem
  · exact full_point_17_mem
  · exact full_point_18_mem
  · exact full_point_19_mem
  · exact full_point_20_mem
  · exact full_point_21_mem

theorem full_images_inside :
    ∀ i : Fin 22,
      intervalStrictInside (fullImageCachedQ i) (unitBox (n := 22) i) = true := by
  intro i
  fin_cases i
  · exact full_image_0_inside
  · exact full_image_1_inside
  · exact full_image_2_inside
  · exact full_image_3_inside
  · exact full_image_4_inside
  · exact full_image_5_inside
  · exact full_image_6_inside
  · exact full_image_7_inside
  · exact full_image_8_inside
  · exact full_image_9_inside
  · exact full_image_10_inside
  · exact full_image_11_inside
  · exact full_image_12_inside
  · exact full_image_13_inside
  · exact full_image_14_inside
  · exact full_image_15_inside
  · exact full_image_16_inside
  · exact full_image_17_inside
  · exact full_image_18_inside
  · exact full_image_19_inside
  · exact full_image_20_inside
  · exact full_image_21_inside

theorem full_unique_scaled :
    ∃! u, FinBoxMem u (unitBox (n := 22)) ∧ SystemZero fullExpr u := by
  exact uniqueSystemZero_of_certified_contraction_values
    fullExpr fullExpr_supported (unitBox (n := 22)) (zeroCenter (n := 22))
    full_center_mem fullY cfg qTarget qTarget_nonneg qTarget_lt_one
    (by simpa [fullPJ] using full_bound_le)
    fullPointCache full_point_values_mem full_images_inside

end PartALeanCert
end GerverSofa
