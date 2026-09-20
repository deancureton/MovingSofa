import GerverSofa.KernelOnly.PartE.E24KC2ProofHelpers

/-! KC6R4 explicit terminal-certificate subtree. No adaptive search. -/
noncomputable section

namespace GerverSofa
namespace PartE

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0000220021__c0__c0__c1 :
    adaptiveCoverCheck 6 (childLH (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLH (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))
    (by
      have h : ((childLL (childLH (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))) h)
    (by
      have h : ((childLH (childLH (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childLH (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))
        (by
          have h : ((childLL (childHL (childLH (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childLH (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))) h)
        (by
          have h : ((childLH (childHL (childLH (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childLH (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))) h)
        (by
          have h : ((childHL (childHL (childLH (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childLH (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))) h)
        (by
          have h : ((childHH (childHL (childLH (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childLH (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childLH (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))
        (by
          have h : ((childLL (childHH (childLH (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childLH (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))) h)
        (by
          have h : ((childLH (childHH (childLH (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childLH (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))) h)
        (by
          have h : ((childHL (childHH (childLH (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childLH (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))) h)
        (by
          have h : ((childHH (childHH (childLH (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childLH (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))) h))

end PartE
end GerverSofa
