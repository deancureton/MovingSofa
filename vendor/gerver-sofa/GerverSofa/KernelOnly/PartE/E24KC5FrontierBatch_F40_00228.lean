import GerverSofa.KernelOnly.PartE.E24KC2ProofHelpers

/-! E24KC5 checkpoint-aware kernel batch. -/
noncomputable section

namespace GerverSofa
namespace PartE

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiBelowLeaf32211 :
    adaptiveCoverCheck 9 (childLH (childLH (childHL (childHL (childHH e24PhiBelowRoot))))) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiBelowLeaf32213 :
    adaptiveCoverCheck 9 (childHH (childLH (childHL (childHL (childHH e24PhiBelowRoot))))) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiBelowLeaf32231 :
    adaptiveCoverCheck 9 (childLH (childHH (childHL (childHL (childHH e24PhiBelowRoot))))) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiBelowLeaf32300 :
    adaptiveCoverCheck 9 (childLL (childLL (childHH (childHL (childHH e24PhiBelowRoot))))) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiBelowLeaf32301 :
    adaptiveCoverCheck 9 (childLH (childLL (childHH (childHL (childHH e24PhiBelowRoot))))) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiBelowLeaf32302 :
    adaptiveCoverCheck 9 (childHL (childLL (childHH (childHL (childHH e24PhiBelowRoot))))) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiBelowLeaf32303 :
    adaptiveCoverCheck 9 (childHH (childLL (childHH (childHL (childHH e24PhiBelowRoot))))) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiBelowLeaf32310 :
    adaptiveCoverCheck 9 (childLL (childLH (childHH (childHL (childHH e24PhiBelowRoot))))) = true := by
  decide +kernel

end PartE
end GerverSofa
