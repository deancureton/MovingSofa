import GerverSofa.KernelOnly.PartE.E24KC2ProofHelpers

/-! KC6R4 explicit terminal-certificate subtree. No adaptive search. -/
noncomputable section

namespace GerverSofa
namespace PartE

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111133113__c1__c1__c1__c2__c3 :
    adaptiveCoverCheck 4 (childHH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))
    (by
      have h : ((childLL (childHH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childHH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))) h)
    (by
      have h : ((childLH (childHH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childHH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))) h)
    (by
      have h : ((childHL (childHH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childHH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))) h)
    (by
      have h : ((childHH (childHH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childHH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))) h)

end PartE
end GerverSofa
