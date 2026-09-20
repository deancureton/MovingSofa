import GerverSofa.KernelOnly.PartE.E24KC2ProofHelpers

noncomputable section

namespace GerverSofa
namespace PartE

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1101101__c0__c0__c1__c1__c2 :
    adaptiveCoverCheck 4 (childHL (childLH (childLH (childLL (childLL (childLH (childLL (childLH (childLH (childLL (childLH (childLH e24PhiAboveRoot)))))))))))) = true := by
  decide +kernel

end PartE
end GerverSofa
