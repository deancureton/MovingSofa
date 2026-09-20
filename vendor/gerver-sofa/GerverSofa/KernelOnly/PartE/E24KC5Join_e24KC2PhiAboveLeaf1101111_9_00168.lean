import GerverSofa.KernelOnly.PartE.E24KC5Direct_e24KC2PhiAboveLeaf1101111__c2_8_00166
import GerverSofa.KernelOnly.PartE.E24KC5Direct_e24KC2PhiAboveLeaf1101111__c3_8_00167
import GerverSofa.KernelOnly.PartE.E24KC5Join_e24KC2PhiAboveLeaf1101111__c0_8_00159
import GerverSofa.KernelOnly.PartE.E24KC5Join_e24KC2PhiAboveLeaf1101111__c1_8_00165

noncomputable section

namespace GerverSofa
namespace PartE

theorem e24KC2PhiAboveLeaf1101111 :
    adaptiveCoverCheck 9 (childLH (childLH (childLH (childLH (childLL (childLH (childLH e24PhiAboveRoot))))))) = true :=
  adaptiveCoverCheck_succ_of_children 8 (childLH (childLH (childLH (childLH (childLL (childLH (childLH e24PhiAboveRoot)))))))
    e24KC2PhiAboveLeaf1101111__c0 e24KC2PhiAboveLeaf1101111__c1 e24KC2PhiAboveLeaf1101111__c2 e24KC2PhiAboveLeaf1101111__c3

end PartE
end GerverSofa
