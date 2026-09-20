import GerverSofa.KernelOnly.PartE.E24KC5Direct_e24KC2PhiAboveLeaf1110000__c1_8_00179
import GerverSofa.KernelOnly.PartE.E24KC5Direct_e24KC2PhiAboveLeaf1110000__c2_8_00180
import GerverSofa.KernelOnly.PartE.E24KC5Direct_e24KC2PhiAboveLeaf1110000__c3_8_00181
import GerverSofa.KernelOnly.PartE.E24KC5Join_e24KC2PhiAboveLeaf1110000__c0_8_00178

noncomputable section

namespace GerverSofa
namespace PartE

theorem e24KC2PhiAboveLeaf1110000 :
    adaptiveCoverCheck 9 (childLL (childLL (childLL (childLL (childLH (childLH (childLH e24PhiAboveRoot))))))) = true :=
  adaptiveCoverCheck_succ_of_children 8 (childLL (childLL (childLL (childLL (childLH (childLH (childLH e24PhiAboveRoot)))))))
    e24KC2PhiAboveLeaf1110000__c0 e24KC2PhiAboveLeaf1110000__c1 e24KC2PhiAboveLeaf1110000__c2 e24KC2PhiAboveLeaf1110000__c3

end PartE
end GerverSofa
