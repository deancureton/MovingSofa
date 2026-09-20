import GerverSofa.KernelOnly.PartE.E24KC5Direct_e24KC2PhiAboveLeaf1101101__c2_8_00109
import GerverSofa.KernelOnly.PartE.E24KC5Direct_e24KC2PhiAboveLeaf1101101__c3_8_00110
import GerverSofa.KernelOnly.PartE.E24KC5Join_e24KC2PhiAboveLeaf1101101__c0_8_00077
import GerverSofa.KernelOnly.PartE.E24KC5Join_e24KC2PhiAboveLeaf1101101__c1_8_00108

noncomputable section

namespace GerverSofa
namespace PartE

theorem e24KC2PhiAboveLeaf1101101 :
    adaptiveCoverCheck 9 (childLH (childLL (childLH (childLH (childLL (childLH (childLH e24PhiAboveRoot))))))) = true :=
  adaptiveCoverCheck_succ_of_children 8 (childLH (childLL (childLH (childLH (childLL (childLH (childLH e24PhiAboveRoot)))))))
    e24KC2PhiAboveLeaf1101101__c0 e24KC2PhiAboveLeaf1101101__c1 e24KC2PhiAboveLeaf1101101__c2 e24KC2PhiAboveLeaf1101101__c3

end PartE
end GerverSofa
