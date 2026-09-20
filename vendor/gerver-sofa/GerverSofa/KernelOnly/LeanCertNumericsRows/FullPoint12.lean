import GerverSofa.KernelOnly.LeanCertNumericsRows.Full12

/-!
# Direct 22D certificate, point residual 12

The expensive transcendental evaluation is checked once for this single
coordinate and then replaced by a small rational cache interval downstream.
-/

noncomputable section

namespace GerverSofa
namespace PartALeanCert

open LeanCert.Core
open LeanCert.Engine

set_option maxRecDepth 180000 in
set_option maxHeartbeats 120000000 in
theorem full_point_12_contained :
    intervalContained
      (pointEvalIntervalsKernel fullExpr (zeroCenter (n := 22)) cfg (12 : Fin 22))
      (fullPointCache (12 : Fin 22)) := by
  constructor <;> decide +kernel

theorem full_point_12_mem :
    systemEval fullExpr
        (fun k => ((zeroCenter (n := 22) k : ℚ) : ℝ)) (12 : Fin 22) ∈
      fullPointCache (12 : Fin 22) :=
  mem_of_intervalContained
    (systemEval_mem_pointEvalIntervalsKernel_const
      fullExpr fullExpr_supported (zeroCenter (n := 22)) cfg (12 : Fin 22))
    full_point_12_contained

end PartALeanCert
end GerverSofa
