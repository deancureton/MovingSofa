import GerverSofa.KernelOnly.PartE.E24KC2ProofHelpers

/-! E24KC5 checkpoint-aware kernel batch. -/
noncomputable section

namespace GerverSofa
namespace PartE

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1111101 :
    adaptiveCoverCheck 9 (childLH (childLL (childLH (childLH (childLH (childLH (childLH e24PhiAboveRoot))))))) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1111102 :
    adaptiveCoverCheck 9 (childHL (childLL (childLH (childLH (childLH (childLH (childLH e24PhiAboveRoot))))))) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1111103 :
    adaptiveCoverCheck 9 (childHH (childLL (childLH (childLH (childLH (childLH (childLH e24PhiAboveRoot))))))) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1111110 :
    adaptiveCoverCheck 9 (childLL (childLH (childLH (childLH (childLH (childLH (childLH e24PhiAboveRoot))))))) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1111111 :
    adaptiveCoverCheck 9 (childLH (childLH (childLH (childLH (childLH (childLH (childLH e24PhiAboveRoot))))))) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1111112 :
    adaptiveCoverCheck 9 (childHL (childLH (childLH (childLH (childLH (childLH (childLH e24PhiAboveRoot))))))) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1111113 :
    adaptiveCoverCheck 9 (childHH (childLH (childLH (childLH (childLH (childLH (childLH e24PhiAboveRoot))))))) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1111131 :
    adaptiveCoverCheck 9 (childLH (childHH (childLH (childLH (childLH (childLH (childLH e24PhiAboveRoot))))))) = true := by
  decide +kernel

end PartE
end GerverSofa
