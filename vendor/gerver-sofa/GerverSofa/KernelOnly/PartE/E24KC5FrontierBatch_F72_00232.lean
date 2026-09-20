import GerverSofa.KernelOnly.PartE.E24KC2ProofHelpers

/-! E24KC5 checkpoint-aware kernel batch. -/
noncomputable section

namespace GerverSofa
namespace PartE

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiBelowLeaf33031 :
    adaptiveCoverCheck 9 (childLH (childHH (childLL (childHH (childHH e24PhiBelowRoot))))) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiBelowLeaf33032 :
    adaptiveCoverCheck 9 (childHL (childHH (childLL (childHH (childHH e24PhiBelowRoot))))) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiBelowLeaf33033 :
    adaptiveCoverCheck 9 (childHH (childHH (childLL (childHH (childHH e24PhiBelowRoot))))) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiBelowLeaf33102 :
    adaptiveCoverCheck 9 (childHL (childLL (childLH (childHH (childHH e24PhiBelowRoot))))) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiBelowLeaf33120 :
    adaptiveCoverCheck 9 (childLL (childHL (childLH (childHH (childHH e24PhiBelowRoot))))) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiBelowLeaf33121 :
    adaptiveCoverCheck 9 (childLH (childHL (childLH (childHH (childHH e24PhiBelowRoot))))) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiBelowLeaf33122 :
    adaptiveCoverCheck 9 (childHL (childHL (childLH (childHH (childHH e24PhiBelowRoot))))) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiBelowLeaf33123 :
    adaptiveCoverCheck 9 (childHH (childHL (childLH (childHH (childHH e24PhiBelowRoot))))) = true := by
  decide +kernel

end PartE
end GerverSofa
