import GerverSofa.KernelOnly.PartE.E24KC2ProofHelpers

/-! E24KC5 checkpoint-aware kernel batch. -/
noncomputable section

namespace GerverSofa
namespace PartE

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiBelowLeaf32331 :
    adaptiveCoverCheck 9 (childLH (childHH (childHH (childHL (childHH e24PhiBelowRoot))))) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiBelowLeaf32332 :
    adaptiveCoverCheck 9 (childHL (childHH (childHH (childHL (childHH e24PhiBelowRoot))))) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiBelowLeaf32333 :
    adaptiveCoverCheck 9 (childHH (childHH (childHH (childHL (childHH e24PhiBelowRoot))))) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiBelowLeaf33000 :
    adaptiveCoverCheck 9 (childLL (childLL (childLL (childHH (childHH e24PhiBelowRoot))))) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiBelowLeaf33001 :
    adaptiveCoverCheck 9 (childLH (childLL (childLL (childHH (childHH e24PhiBelowRoot))))) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiBelowLeaf33002 :
    adaptiveCoverCheck 9 (childHL (childLL (childLL (childHH (childHH e24PhiBelowRoot))))) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiBelowLeaf33003 :
    adaptiveCoverCheck 9 (childHH (childLL (childLL (childHH (childHH e24PhiBelowRoot))))) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiBelowLeaf33010 :
    adaptiveCoverCheck 9 (childLL (childLH (childLL (childHH (childHH e24PhiBelowRoot))))) = true := by
  decide +kernel

end PartE
end GerverSofa
