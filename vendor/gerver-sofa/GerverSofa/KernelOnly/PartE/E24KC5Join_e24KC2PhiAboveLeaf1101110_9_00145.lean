import GerverSofa.KernelOnly.PartE.E24KC5Direct_e24KC2PhiAboveLeaf1101110__c2_8_00143
import GerverSofa.KernelOnly.PartE.E24KC5Direct_e24KC2PhiAboveLeaf1101110__c3_8_00144
import GerverSofa.KernelOnly.PartE.E24KC5Join_e24KC2PhiAboveLeaf1101110__c0_8_00136
import GerverSofa.KernelOnly.PartE.E24KC5Join_e24KC2PhiAboveLeaf1101110__c1_8_00142

noncomputable section

namespace GerverSofa
namespace PartE

theorem e24KC2PhiAboveLeaf1101110 :
    adaptiveCoverCheck 9 (childLL (childLH (childLH (childLH (childLL (childLH (childLH e24PhiAboveRoot))))))) = true :=
  adaptiveCoverCheck_succ_of_children 8 (childLL (childLH (childLH (childLH (childLL (childLH (childLH e24PhiAboveRoot)))))))
    e24KC2PhiAboveLeaf1101110__c0 e24KC2PhiAboveLeaf1101110__c1 e24KC2PhiAboveLeaf1101110__c2 e24KC2PhiAboveLeaf1101110__c3

end PartE
end GerverSofa
