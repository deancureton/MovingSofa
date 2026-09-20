import GerverSofa.KernelOnly.PartE.E24KC2ProofHelpers

noncomputable section

namespace GerverSofa
namespace PartE

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiBelowLeaf33233__c2__c2__c3__c2__c3__c2 :
    adaptiveCoverCheck 3 (childHL (childHH (childHL (childHH (childHL (childHL (childHH (childHH (childHL (childHH (childHH e24PhiBelowRoot))))))))))) = true := by
  decide +kernel

end PartE
end GerverSofa
