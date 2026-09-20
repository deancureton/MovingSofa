import GerverSofa.KernelOnly.PartE.E24KC2ProofHelpers

/-! E24KC5 checkpoint-aware kernel batch. -/
noncomputable section

namespace GerverSofa
namespace PartE

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiBelowLeaf33303 :
    adaptiveCoverCheck 9 (childHH (childLL (childHH (childHH (childHH e24PhiBelowRoot))))) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiBelowLeaf33310 :
    adaptiveCoverCheck 9 (childLL (childLH (childHH (childHH (childHH e24PhiBelowRoot))))) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiBelowLeaf33311 :
    adaptiveCoverCheck 9 (childLH (childLH (childHH (childHH (childHH e24PhiBelowRoot))))) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiBelowLeaf33312 :
    adaptiveCoverCheck 9 (childHL (childLH (childHH (childHH (childHH e24PhiBelowRoot))))) = true := by
  decide +kernel

end PartE
end GerverSofa
