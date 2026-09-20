import GerverSofa.KernelOnly.PartE.E24KC2ProofHelpers

/-! KC6R4 explicit terminal-certificate subtree. No adaptive search. -/
noncomputable section

namespace GerverSofa
namespace PartE

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0000220021__c0__c1__c0 :
    adaptiveCoverCheck 6 (childLL (childLH (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLL (childLH (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))
    (by
      have h : ((childLL (childLL (childLH (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL (childLH (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))) h)
    (by
      have h : ((childLH (childLL (childLH (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL (childLH (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childLL (childLH (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))
        (by
          have h : ((childLL (childHL (childLL (childLH (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childLL (childLH (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))) h)
        (by
          have h : ((childLH (childHL (childLL (childLH (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childLL (childLH (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))) h)
        (by
          have h : ((childHL (childHL (childLL (childLH (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childLL (childLH (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))) h)
        (by
          have h : ((childHH (childHL (childLL (childLH (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childLL (childLH (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childLL (childLH (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))
        (by
          have h : ((childLL (childHH (childLL (childLH (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childLL (childLH (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))) h)
        (by
          have h : ((childLH (childHH (childLL (childLH (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childLL (childLH (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))) h)
        (by
          have h : ((childHL (childHH (childLL (childLH (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childLL (childLH (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))) h)
        (by
          have h : ((childHH (childHH (childLL (childLH (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childLL (childLH (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))) h))

end PartE
end GerverSofa
