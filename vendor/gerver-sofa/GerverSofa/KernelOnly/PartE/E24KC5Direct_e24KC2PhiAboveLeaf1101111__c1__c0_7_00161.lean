import GerverSofa.KernelOnly.PartE.E24KC2ProofHelpers

noncomputable section

namespace GerverSofa
namespace PartE

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1101111__c1__c0 :
    adaptiveCoverCheck 7 (childLL (childLH (childLH (childLH (childLH (childLH (childLL (childLH (childLH e24PhiAboveRoot))))))))) = true := by
  decide +kernel

end PartE
end GerverSofa
