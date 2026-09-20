import GerverSofa.KernelOnly.LeanCertGerverNumericsCore

noncomputable section

namespace GerverSofa
namespace PartALeanCert

open LeanCert.Core
open LeanCert.Engine

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem reduced_row_0_lt :
    intervalMatrixRowBound reducedPJ (0 : Fin 4) < qTarget := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem reduced_row_1_lt :
    intervalMatrixRowBound reducedPJ (1 : Fin 4) < qTarget := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem reduced_row_2_lt :
    intervalMatrixRowBound reducedPJ (2 : Fin 4) < qTarget := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem reduced_row_3_lt :
    intervalMatrixRowBound reducedPJ (3 : Fin 4) < qTarget := by
  decide +kernel

theorem reduced_bound_lt : intervalMatrixBound reducedPJ < qTarget := by
  apply matrixBound_lt_of_rows reducedPJ qTarget qTarget_pos
  intro i
  fin_cases i
  · exact reduced_row_0_lt
  · exact reduced_row_1_lt
  · exact reduced_row_2_lt
  · exact reduced_row_3_lt

theorem reduced_bound_le : intervalMatrixBound reducedPJ ≤ qTarget :=
  reduced_bound_lt.le

set_option maxRecDepth 150000 in
set_option maxHeartbeats 60000000 in
theorem reduced_image_0_inside :
    intervalStrictInside (reducedImageQ (0 : Fin 4))
      (unitBox (n := 4) (0 : Fin 4)) = true := by
  decide +kernel

set_option maxRecDepth 150000 in
set_option maxHeartbeats 60000000 in
theorem reduced_image_1_inside :
    intervalStrictInside (reducedImageQ (1 : Fin 4))
      (unitBox (n := 4) (1 : Fin 4)) = true := by
  decide +kernel

set_option maxRecDepth 150000 in
set_option maxHeartbeats 60000000 in
theorem reduced_image_2_inside :
    intervalStrictInside (reducedImageQ (2 : Fin 4))
      (unitBox (n := 4) (2 : Fin 4)) = true := by
  decide +kernel

set_option maxRecDepth 150000 in
set_option maxHeartbeats 60000000 in
theorem reduced_image_3_inside :
    intervalStrictInside (reducedImageQ (3 : Fin 4))
      (unitBox (n := 4) (3 : Fin 4)) = true := by
  decide +kernel

theorem reduced_images_inside :
    ∀ i : Fin 4,
      intervalStrictInside (reducedImageQ i) (unitBox (n := 4) i) = true := by
  intro i
  fin_cases i
  · exact reduced_image_0_inside
  · exact reduced_image_1_inside
  · exact reduced_image_2_inside
  · exact reduced_image_3_inside

theorem reduced_unique_scaled :
    ∃! u, FinBoxMem u (unitBox (n := 4)) ∧ SystemZero reducedExpr u := by
  exact uniqueSystemZero_of_certified_contraction
    reducedExpr reducedExpr_supported (unitBox (n := 4)) (zeroCenter (n := 4))
    reduced_center_mem reducedY cfg qTarget qTarget_nonneg qTarget_lt_one
    (by simpa [reducedPJ] using reduced_bound_le)
    reduced_images_inside

end PartALeanCert
end GerverSofa
