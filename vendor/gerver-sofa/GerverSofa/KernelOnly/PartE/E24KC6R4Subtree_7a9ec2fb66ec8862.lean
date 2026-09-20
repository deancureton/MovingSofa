import GerverSofa.KernelOnly.PartE.E24KC2ProofHelpers

/-! KC6R4 explicit terminal-certificate subtree. No adaptive search. -/
noncomputable section

namespace GerverSofa
namespace PartE

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0000220021__c0__c0__c2__c2 :
    adaptiveCoverCheck 5 (childHL (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHL (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))
        (by
          have h : ((childLL (childLL (childHL (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLL (childHL (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))) h)
        (by
          have h : ((childLH (childLL (childHL (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLL (childHL (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))) h)
        (by
          have h : ((childHL (childLL (childHL (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childLL (childHL (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))) h)
        (by
          have h : ((childHH (childLL (childHL (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHL (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))
        (by
          have h : ((childLL (childLH (childHL (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLH (childHL (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))) h)
        (by
          have h : ((childLH (childLH (childHL (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLH (childHL (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))) h)
        (by
          have h : ((childHL (childLH (childHL (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childLH (childHL (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))) h)
        (by
          have h : ((childHH (childLH (childHL (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childLH (childHL (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))) h))
    (by
      have h : ((childHL (childHL (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))) h)
    (by
      have h : ((childHH (childHL (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))) h)

end PartE
end GerverSofa
