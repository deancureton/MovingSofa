import GerverSofa.KernelOnly.LeanCertNumericsRows.Full10

/-!
# Direct 22D certificate, point residual 10

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
theorem full_point_10_contained :
    intervalContained
      (pointEvalIntervalsKernel fullExpr (zeroCenter (n := 22)) cfg (10 : Fin 22))
      (fullPointCache (10 : Fin 22)) := by
  constructor <;> decide +kernel

theorem full_point_10_mem :
    systemEval fullExpr
        (fun k => ((zeroCenter (n := 22) k : ℚ) : ℝ)) (10 : Fin 22) ∈
      fullPointCache (10 : Fin 22) :=
  mem_of_intervalContained
    (systemEval_mem_pointEvalIntervalsKernel_const
      fullExpr fullExpr_supported (zeroCenter (n := 22)) cfg (10 : Fin 22))
    full_point_10_contained

end PartALeanCert
end GerverSofa
