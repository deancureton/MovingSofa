import GerverSofa.KernelOnly.LeanCertGerverNumericsReduced

/-!
# Direct 22D certificate, row 0: Jacobian bound

The row modules form a deliberate dependency chain beginning after the
already-certified reduced 4D module.  Lake therefore checks
only one expensive closed kernel proposition at a time instead of launching
all 22 rows concurrently and exhausting RAM.
-/

noncomputable section

namespace GerverSofa
namespace PartALeanCert

open LeanCert.Core
open LeanCert.Engine

set_option maxRecDepth 100000 in
set_option maxHeartbeats 7000000 in
theorem full_row_0_lt :
    intervalMatrixRowBound fullPJ (0 : Fin 22) < qTarget := by
  decide +kernel

end PartALeanCert
end GerverSofa
