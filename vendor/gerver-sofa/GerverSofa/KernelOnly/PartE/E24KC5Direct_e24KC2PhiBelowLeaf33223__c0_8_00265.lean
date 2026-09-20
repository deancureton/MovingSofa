import GerverSofa.KernelOnly.PartE.E24KC2ProofHelpers

noncomputable section

namespace GerverSofa
namespace PartE

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiBelowLeaf33223__c0 :
    adaptiveCoverCheck 8 (childLL (childHH (childHL (childHL (childHH (childHH e24PhiBelowRoot)))))) = true := by
  decide +kernel

end PartE
end GerverSofa
