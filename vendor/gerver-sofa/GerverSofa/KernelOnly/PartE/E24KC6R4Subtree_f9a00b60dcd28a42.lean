import GerverSofa.KernelOnly.PartE.E24KC2ProofHelpers

/-! KC6R4 explicit terminal-certificate subtree. No adaptive search. -/
noncomputable section

namespace GerverSofa
namespace PartE

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111133113__c0__c2 :
    adaptiveCoverCheck 7 (childHL (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 6 (childHL (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
    (by
      have h : ((childLL (childHL (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHL (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
    (by
      have h : ((childLH (childHL (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHL (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
    (by
      have h : ((childHL (childHL (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHL (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
    (by
      have h : ((childHH (childHL (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHL (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)

end PartE
end GerverSofa
