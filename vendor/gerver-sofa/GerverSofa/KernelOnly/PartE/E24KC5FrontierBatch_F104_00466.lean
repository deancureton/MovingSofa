import GerverSofa.KernelOnly.PartE.E24KC2ProofHelpers

/-! E24KC5 checkpoint-aware kernel batch. -/
noncomputable section

namespace GerverSofa
namespace PartE

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiBelowLeaf33313 :
    adaptiveCoverCheck 9 (childHH (childLH (childHH (childHH (childHH e24PhiBelowRoot))))) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiBelowLeaf33320 :
    adaptiveCoverCheck 9 (childLL (childHL (childHH (childHH (childHH e24PhiBelowRoot))))) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiBelowLeaf33321 :
    adaptiveCoverCheck 9 (childLH (childHL (childHH (childHH (childHH e24PhiBelowRoot))))) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiBelowLeaf33322 :
    adaptiveCoverCheck 9 (childHL (childHL (childHH (childHH (childHH e24PhiBelowRoot))))) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiBelowLeaf33323 :
    adaptiveCoverCheck 9 (childHH (childHL (childHH (childHH (childHH e24PhiBelowRoot))))) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiBelowLeaf33330 :
    adaptiveCoverCheck 9 (childLL (childHH (childHH (childHH (childHH e24PhiBelowRoot))))) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiBelowLeaf33331 :
    adaptiveCoverCheck 9 (childLH (childHH (childHH (childHH (childHH e24PhiBelowRoot))))) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiBelowLeaf33332 :
    adaptiveCoverCheck 9 (childHL (childHH (childHH (childHH (childHH e24PhiBelowRoot))))) = true := by
  decide +kernel

end PartE
end GerverSofa
