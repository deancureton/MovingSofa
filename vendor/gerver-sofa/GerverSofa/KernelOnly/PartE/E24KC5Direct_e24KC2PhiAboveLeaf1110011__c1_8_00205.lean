import GerverSofa.KernelOnly.PartE.E24KC2ProofHelpers

noncomputable section

namespace GerverSofa
namespace PartE

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1110011__c1 :
    adaptiveCoverCheck 8 (childLH (childLH (childLH (childLL (childLL (childLH (childLH (childLH e24PhiAboveRoot)))))))) = true := by
  decide +kernel

end PartE
end GerverSofa
