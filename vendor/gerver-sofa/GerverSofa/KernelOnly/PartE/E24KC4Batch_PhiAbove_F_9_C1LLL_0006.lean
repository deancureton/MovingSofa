import GerverSofa.KernelOnly.PartE.E24KC2ProofHelpers

/-! E24KC4 auto-tuned batched kernel certificates. -/
noncomputable section

namespace GerverSofa
namespace PartE

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1100111 :
    adaptiveCoverCheck 9 (childLH (childLH (childLH (childLL (childLL (childLH (childLH e24PhiAboveRoot))))))) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1101000 :
    adaptiveCoverCheck 9 (childLL (childLL (childLL (childLH (childLL (childLH (childLH e24PhiAboveRoot))))))) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1101001 :
    adaptiveCoverCheck 9 (childLH (childLL (childLL (childLH (childLL (childLH (childLH e24PhiAboveRoot))))))) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1101010 :
    adaptiveCoverCheck 9 (childLL (childLH (childLL (childLH (childLL (childLH (childLH e24PhiAboveRoot))))))) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1101011 :
    adaptiveCoverCheck 9 (childLH (childLH (childLL (childLH (childLL (childLH (childLH e24PhiAboveRoot))))))) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1101012 :
    adaptiveCoverCheck 9 (childHL (childLH (childLL (childLH (childLL (childLH (childLH e24PhiAboveRoot))))))) = true := by
  decide +kernel

end PartE
end GerverSofa
