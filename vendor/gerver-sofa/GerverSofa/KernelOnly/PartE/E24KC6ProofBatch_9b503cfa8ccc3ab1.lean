import GerverSofa.KernelOnly.PartE.E24KC5Direct_e24KC2ThetaAboveLeaf0000220020__c1__c2_7_00028
import GerverSofa.KernelOnly.PartE.E24KC5Direct_e24KC2ThetaAboveLeaf0000220020__c1__c3_7_00029
import GerverSofa.KernelOnly.PartE.E24KC5Join_e24KC2ThetaAboveLeaf0000220020__c0_8_00603
import GerverSofa.KernelOnly.PartE.E24KC5Join_e24KC2ThetaAboveLeaf0000220020__c1__c0_7_00640
import GerverSofa.KernelOnly.PartE.E24KC5Join_e24KC2ThetaAboveLeaf0000220020__c1__c1_7_00027

/-! E24KC6 explicit proof-producing certificate batch. -/
noncomputable section

namespace GerverSofa
namespace PartE

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0000220020 :
    adaptiveCoverCheck 9 (childLL (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact e24KC2ThetaAboveLeaf0000220020__c0)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          exact e24KC2ThetaAboveLeaf0000220020__c1__c0)
        (by
          exact e24KC2ThetaAboveLeaf0000220020__c1__c1)
        (by
          exact e24KC2ThetaAboveLeaf0000220020__c1__c2)
        (by
          exact e24KC2ThetaAboveLeaf0000220020__c1__c3))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHL (childLL (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childLL (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHL (childLL (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLL (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHL (childLL (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLL (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHL (childLL (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLL (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHH (childLL (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLL (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHH (childLL (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLL (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHH (childLL (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLL (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHH (childLL (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLL (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))

end PartE
end GerverSofa
