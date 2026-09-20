import GerverSofa.KernelOnly.PartE.E24KC2ProofHelpers

/-! KC6R4 explicit terminal-certificate subtree. No adaptive search. -/
noncomputable section

namespace GerverSofa
namespace PartE

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111133113__c3 :
    adaptiveCoverCheck 8 (childHH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
    (by
      have h : ((childLL (childHH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)

end PartE
end GerverSofa
