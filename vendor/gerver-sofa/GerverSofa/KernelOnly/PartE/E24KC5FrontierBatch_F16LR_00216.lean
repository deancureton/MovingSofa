import GerverSofa.KernelOnly.PartE.E24KC2ProofHelpers

/-! E24KC5 checkpoint-aware kernel batch. -/
noncomputable section

namespace GerverSofa
namespace PartE

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1110103 :
    adaptiveCoverCheck 9 (childHH (childLL (childLH (childLL (childLH (childLH (childLH e24PhiAboveRoot))))))) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1110110 :
    adaptiveCoverCheck 9 (childLL (childLH (childLH (childLL (childLH (childLH (childLH e24PhiAboveRoot))))))) = true := by
  decide +kernel

end PartE
end GerverSofa
