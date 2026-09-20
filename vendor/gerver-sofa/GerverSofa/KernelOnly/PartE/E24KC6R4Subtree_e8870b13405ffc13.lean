import GerverSofa.KernelOnly.PartE.E24KC2ProofHelpers

/-! KC6R4 explicit terminal-certificate subtree. No adaptive search. -/
noncomputable section

namespace GerverSofa
namespace PartE

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111133113__c1__c1__c1__c3__c0 :
    adaptiveCoverCheck 4 (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childLL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))
        (by
          exact adaptiveCoverCheck_succ_of_children 1 (childLL (childLL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))
            (by
              exact adaptiveCoverCheck_succ_of_children 0 (childLL (childLL (childLL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))
                (by
                  have h : ((childLL (childLL (childLL (childLL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childLL (childLL (childLL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                (by
                  have h : ((childLH (childLL (childLL (childLL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childLL (childLL (childLL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                (by
                  have h : ((childHL (childLL (childLL (childLL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childLL (childLL (childLL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                (by
                  have h : ((childHH (childLL (childLL (childLL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childLL (childLL (childLL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 0 (childLH (childLL (childLL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))
                (by
                  have h : ((childLL (childLH (childLL (childLL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childLH (childLL (childLL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                (by
                  have h : ((childLH (childLH (childLL (childLL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childLH (childLL (childLL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                (by
                  have h : ((childHL (childLH (childLL (childLL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childLH (childLL (childLL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                (by
                  have h : ((childHH (childLH (childLL (childLL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childLH (childLL (childLL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 0 (childHL (childLL (childLL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))
                (by
                  have h : ((childLL (childHL (childLL (childLL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childHL (childLL (childLL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                (by
                  have h : ((childLH (childHL (childLL (childLL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childHL (childLL (childLL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                (by
                  have h : ((childHL (childHL (childLL (childLL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childHL (childLL (childLL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                (by
                  have h : ((childHH (childHL (childLL (childLL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childHL (childLL (childLL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 0 (childHH (childLL (childLL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))
                (by
                  have h : ((childLL (childHH (childLL (childLL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childHH (childLL (childLL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                (by
                  have h : ((childLH (childHH (childLL (childLL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childHH (childLL (childLL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                (by
                  have h : ((childHL (childHH (childLL (childLL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childHH (childLL (childLL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                (by
                  have h : ((childHH (childHH (childLL (childLL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childHH (childLL (childLL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)))
        (by
          exact adaptiveCoverCheck_succ_of_children 1 (childLH (childLL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))
            (by
              exact adaptiveCoverCheck_succ_of_children 0 (childLL (childLH (childLL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))
                (by
                  have h : ((childLL (childLL (childLH (childLL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childLL (childLH (childLL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                (by
                  have h : ((childLH (childLL (childLH (childLL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childLL (childLH (childLL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                (by
                  have h : ((childHL (childLL (childLH (childLL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childLL (childLH (childLL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                (by
                  have h : ((childHH (childLL (childLH (childLL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childLL (childLH (childLL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 0 (childLH (childLH (childLL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))
                (by
                  have h : ((childLL (childLH (childLH (childLL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childLH (childLH (childLL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                (by
                  have h : ((childLH (childLH (childLH (childLL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childLH (childLH (childLL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                (by
                  have h : ((childHL (childLH (childLH (childLL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childLH (childLH (childLL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                (by
                  have h : ((childHH (childLH (childLH (childLL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childLH (childLH (childLL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 0 (childHL (childLH (childLL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))
                (by
                  have h : ((childLL (childHL (childLH (childLL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childHL (childLH (childLL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                (by
                  have h : ((childLH (childHL (childLH (childLL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childHL (childLH (childLL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                (by
                  have h : ((childHL (childHL (childLH (childLL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childHL (childLH (childLL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                (by
                  have h : ((childHH (childHL (childLH (childLL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childHL (childLH (childLL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 0 (childHH (childLH (childLL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))
                (by
                  have h : ((childLL (childHH (childLH (childLL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childHH (childLH (childLL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                (by
                  have h : ((childLH (childHH (childLH (childLL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childHH (childLH (childLL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                (by
                  have h : ((childHL (childHH (childLH (childLL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childHH (childLH (childLL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                (by
                  have h : ((childHH (childHH (childLH (childLL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childHH (childLH (childLL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)))
        (by
          exact adaptiveCoverCheck_succ_of_children 1 (childHL (childLL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))
            (by
              have h : ((childLL (childHL (childLL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHL (childLL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
            (by
              have h : ((childLH (childHL (childLL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHL (childLL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
            (by
              have h : ((childHL (childHL (childLL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHL (childLL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
            (by
              have h : ((childHH (childHL (childLL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHL (childLL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 1 (childHH (childLL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))
            (by
              have h : ((childLL (childHH (childLL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHH (childLL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
            (by
              have h : ((childLH (childHH (childLL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHH (childLL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
            (by
              have h : ((childHL (childHH (childLL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHH (childLL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
            (by
              have h : ((childHH (childHH (childLL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHH (childLL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))
        (by
          exact adaptiveCoverCheck_succ_of_children 1 (childLL (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))
            (by
              exact adaptiveCoverCheck_succ_of_children 0 (childLL (childLL (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))
                (by
                  have h : ((childLL (childLL (childLL (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childLL (childLL (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                (by
                  have h : ((childLH (childLL (childLL (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childLL (childLL (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                (by
                  have h : ((childHL (childLL (childLL (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childLL (childLL (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                (by
                  have h : ((childHH (childLL (childLL (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childLL (childLL (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 0 (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))
                (by
                  have h : ((childLL (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                (by
                  have h : ((childLH (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                (by
                  have h : ((childHL (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                (by
                  have h : ((childHH (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 0 (childHL (childLL (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))
                (by
                  have h : ((childLL (childHL (childLL (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childHL (childLL (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                (by
                  have h : ((childLH (childHL (childLL (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childHL (childLL (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                (by
                  have h : ((childHL (childHL (childLL (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childHL (childLL (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                (by
                  have h : ((childHH (childHL (childLL (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childHL (childLL (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 0 (childHH (childLL (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))
                (by
                  have h : ((childLL (childHH (childLL (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childHH (childLL (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                (by
                  have h : ((childLH (childHH (childLL (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childHH (childLL (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                (by
                  have h : ((childHL (childHH (childLL (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childHH (childLL (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                (by
                  have h : ((childHH (childHH (childLL (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childHH (childLL (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)))
        (by
          exact adaptiveCoverCheck_succ_of_children 1 (childLH (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))
            (by
              exact adaptiveCoverCheck_succ_of_children 0 (childLL (childLH (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))
                (by
                  have h : ((childLL (childLL (childLH (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childLL (childLH (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                (by
                  have h : ((childLH (childLL (childLH (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childLL (childLH (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                (by
                  have h : ((childHL (childLL (childLH (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childLL (childLH (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                (by
                  have h : ((childHH (childLL (childLH (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childLL (childLH (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 0 (childLH (childLH (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))
                (by
                  have h : ((childLL (childLH (childLH (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childLH (childLH (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                (by
                  have h : ((childLH (childLH (childLH (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childLH (childLH (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                (by
                  have h : ((childHL (childLH (childLH (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childLH (childLH (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                (by
                  have h : ((childHH (childLH (childLH (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childLH (childLH (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 0 (childHL (childLH (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))
                (by
                  have h : ((childLL (childHL (childLH (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childHL (childLH (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                (by
                  have h : ((childLH (childHL (childLH (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childHL (childLH (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                (by
                  have h : ((childHL (childHL (childLH (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childHL (childLH (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                (by
                  have h : ((childHH (childHL (childLH (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childHL (childLH (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 0 (childHH (childLH (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))
                (by
                  have h : ((childLL (childHH (childLH (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childHH (childLH (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                (by
                  have h : ((childLH (childHH (childLH (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childHH (childLH (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                (by
                  have h : ((childHL (childHH (childLH (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childHH (childLH (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                (by
                  have h : ((childHH (childHH (childLH (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childHH (childLH (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)))
        (by
          exact adaptiveCoverCheck_succ_of_children 1 (childHL (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))
            (by
              have h : ((childLL (childHL (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHL (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
            (by
              have h : ((childLH (childHL (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHL (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
            (by
              have h : ((childHL (childHL (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHL (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
            (by
              have h : ((childHH (childHL (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHL (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 1 (childHH (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))
            (by
              have h : ((childLL (childHH (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHH (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
            (by
              exact adaptiveCoverCheck_succ_of_children 0 (childLH (childHH (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))
                (by
                  have h : ((childLL (childLH (childHH (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childLH (childHH (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                (by
                  have h : ((childLH (childLH (childHH (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childLH (childHH (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                (by
                  have h : ((childHL (childLH (childHH (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childLH (childHH (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                (by
                  have h : ((childHH (childLH (childHH (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childLH (childHH (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h))
            (by
              have h : ((childHL (childHH (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHH (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
            (by
              have h : ((childHH (childHH (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHH (childLH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childHL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))
        (by
          have h : ((childLL (childHL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL (childHL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)
        (by
          have h : ((childLH (childHL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH (childHL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)
        (by
          have h : ((childHL (childHL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL (childHL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)
        (by
          have h : ((childHH (childHL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH (childHL (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childHH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))
        (by
          have h : ((childLL (childHH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL (childHH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)
        (by
          have h : ((childLH (childHH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH (childHH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)
        (by
          have h : ((childHL (childHH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL (childHH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)
        (by
          have h : ((childHH (childHH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH (childHH (childLL (childHH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h))

end PartE
end GerverSofa
