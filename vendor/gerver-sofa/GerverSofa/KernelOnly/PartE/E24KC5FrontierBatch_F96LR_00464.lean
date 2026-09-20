import GerverSofa.KernelOnly.PartE.E24KC2ProofHelpers

/-! E24KC5 checkpoint-aware kernel batch. -/
noncomputable section

namespace GerverSofa
namespace PartE

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiBelowLeaf33301 :
    adaptiveCoverCheck 9 (childLH (childLL (childHH (childHH (childHH e24PhiBelowRoot))))) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiBelowLeaf33302 :
    adaptiveCoverCheck 9 (childHL (childLL (childHH (childHH (childHH e24PhiBelowRoot))))) = true := by
  decide +kernel

end PartE
end GerverSofa
