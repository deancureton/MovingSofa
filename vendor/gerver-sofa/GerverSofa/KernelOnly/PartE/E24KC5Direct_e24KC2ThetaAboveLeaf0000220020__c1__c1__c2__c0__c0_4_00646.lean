import GerverSofa.KernelOnly.PartE.E24KC2ProofHelpers

noncomputable section

namespace GerverSofa
namespace PartE

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000220020__c1__c1__c2__c0__c0 :
    adaptiveCoverCheck 4 (childLL (childLL (childHL (childLH (childLH (childLL (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))) = true := by
  decide +kernel

end PartE
end GerverSofa
