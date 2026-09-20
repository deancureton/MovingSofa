import GerverSofa.KernelOnly.LeanCertNumericsRows.FullImage09

/-!
# Direct 22D certificate, row 10: Jacobian bound

The row modules form a deliberate dependency chain.  Lake therefore checks
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
theorem full_row_10_lt :
    intervalMatrixRowBound fullPJ (10 : Fin 22) < qTarget := by
  decide +kernel

end PartALeanCert
end GerverSofa
