import GerverSofa.KernelOnly.LeanCertNumericsRows.Full02

/-!
# Direct 22D certificate, point residual 2

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
theorem full_point_2_contained :
    intervalContained
      (pointEvalIntervalsKernel fullExpr (zeroCenter (n := 22)) cfg (2 : Fin 22))
      (fullPointCache (2 : Fin 22)) := by
  constructor <;> decide +kernel

theorem full_point_2_mem :
    systemEval fullExpr
        (fun k => ((zeroCenter (n := 22) k : ℚ) : ℝ)) (2 : Fin 22) ∈
      fullPointCache (2 : Fin 22) :=
  mem_of_intervalContained
    (systemEval_mem_pointEvalIntervalsKernel_const
      fullExpr fullExpr_supported (zeroCenter (n := 22)) cfg (2 : Fin 22))
    full_point_2_contained

end PartALeanCert
end GerverSofa
