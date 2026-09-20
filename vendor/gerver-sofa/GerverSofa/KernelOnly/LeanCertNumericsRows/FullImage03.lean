import GerverSofa.KernelOnly.LeanCertNumericsRows.FullPoint03

/-!
# Direct 22D certificate, row 3: strict self-map image

This theorem is isolated from the Jacobian-row theorem so each Lean process
checks one heavy proposition and then releases its memory before the next
module in the serial chain begins.
-/

noncomputable section

namespace GerverSofa
namespace PartALeanCert

open LeanCert.Core
open LeanCert.Engine

set_option maxRecDepth 150000 in
set_option maxHeartbeats 20000000 in
theorem full_image_3_inside :
    intervalStrictInside (fullImageCachedQ (3 : Fin 22))
      (unitBox (n := 22) (3 : Fin 22)) = true := by
  decide +kernel

end PartALeanCert
end GerverSofa
