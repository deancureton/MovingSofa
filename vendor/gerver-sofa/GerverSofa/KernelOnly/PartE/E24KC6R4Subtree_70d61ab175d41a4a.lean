import GerverSofa.KernelOnly.PartE.E24KC2ProofHelpers

/-! KC6R4 explicit terminal-certificate subtree. No adaptive search. -/
noncomputable section

namespace GerverSofa
namespace PartE

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111133113__c1__c1__c1__c2__c1 :
    adaptiveCoverCheck 4 (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childLL (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))
        (by
          exact adaptiveCoverCheck_succ_of_children 1 (childLL (childLL (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))
            (by
              have h : ((childLL (childLL (childLL (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childLL (childLL (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
            (by
              have h : ((childLH (childLL (childLL (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childLL (childLL (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
            (by
              exact adaptiveCoverCheck_succ_of_children 0 (childHL (childLL (childLL (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))
                (by
                  have h : ((childLL (childHL (childLL (childLL (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childHL (childLL (childLL (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                (by
                  have h : ((childLH (childHL (childLL (childLL (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childHL (childLL (childLL (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                (by
                  have h : ((childHL (childHL (childLL (childLL (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childHL (childLL (childLL (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                (by
                  have h : ((childHH (childHL (childLL (childLL (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childHL (childLL (childLL (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 0 (childHH (childLL (childLL (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))
                (by
                  have h : ((childLL (childHH (childLL (childLL (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childHH (childLL (childLL (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                (by
                  have h : ((childLH (childHH (childLL (childLL (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childHH (childLL (childLL (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                (by
                  have h : ((childHL (childHH (childLL (childLL (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childHH (childLL (childLL (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                (by
                  have h : ((childHH (childHH (childLL (childLL (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childHH (childLL (childLL (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)))
        (by
          exact adaptiveCoverCheck_succ_of_children 1 (childLH (childLL (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))
            (by
              exact adaptiveCoverCheck_succ_of_children 0 (childLL (childLH (childLL (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))
                (by
                  have h : ((childLL (childLL (childLH (childLL (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childLL (childLH (childLL (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                (by
                  have h : ((childLH (childLL (childLH (childLL (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childLL (childLH (childLL (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                (by
                  have h : ((childHL (childLL (childLH (childLL (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childLL (childLH (childLL (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                (by
                  have h : ((childHH (childLL (childLH (childLL (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childLL (childLH (childLL (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 0 (childLH (childLH (childLL (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))
                (by
                  have h : ((childLL (childLH (childLH (childLL (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childLH (childLH (childLL (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                (by
                  have h : ((childLH (childLH (childLH (childLL (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childLH (childLH (childLL (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                (by
                  have h : ((childHL (childLH (childLH (childLL (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childLH (childLH (childLL (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                (by
                  have h : ((childHH (childLH (childLH (childLL (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childLH (childLH (childLL (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 0 (childHL (childLH (childLL (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))
                (by
                  have h : ((childLL (childHL (childLH (childLL (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childHL (childLH (childLL (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                (by
                  have h : ((childLH (childHL (childLH (childLL (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childHL (childLH (childLL (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                (by
                  have h : ((childHL (childHL (childLH (childLL (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childHL (childLH (childLL (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                (by
                  have h : ((childHH (childHL (childLH (childLL (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childHL (childLH (childLL (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 0 (childHH (childLH (childLL (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))
                (by
                  have h : ((childLL (childHH (childLH (childLL (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childHH (childLH (childLL (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                (by
                  have h : ((childLH (childHH (childLH (childLL (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childHH (childLH (childLL (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                (by
                  have h : ((childHL (childHH (childLH (childLL (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childHH (childLH (childLL (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                (by
                  have h : ((childHH (childHH (childLH (childLL (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childHH (childLH (childLL (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)))
        (by
          exact adaptiveCoverCheck_succ_of_children 1 (childHL (childLL (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))
            (by
              have h : ((childLL (childHL (childLL (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHL (childLL (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
            (by
              have h : ((childLH (childHL (childLL (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHL (childLL (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
            (by
              have h : ((childHL (childHL (childLL (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHL (childLL (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
            (by
              have h : ((childHH (childHL (childLL (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHL (childLL (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 1 (childHH (childLL (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))
            (by
              have h : ((childLL (childHH (childLL (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHH (childLL (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
            (by
              have h : ((childLH (childHH (childLL (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHH (childLL (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
            (by
              have h : ((childHL (childHH (childLL (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHH (childLL (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
            (by
              have h : ((childHH (childHH (childLL (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHH (childLL (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childLH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))
        (by
          exact adaptiveCoverCheck_succ_of_children 1 (childLL (childLH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))
            (by
              exact adaptiveCoverCheck_succ_of_children 0 (childLL (childLL (childLH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))
                (by
                  have h : ((childLL (childLL (childLL (childLH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childLL (childLL (childLH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                (by
                  have h : ((childLH (childLL (childLL (childLH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childLL (childLL (childLH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                (by
                  have h : ((childHL (childLL (childLL (childLH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childLL (childLL (childLH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                (by
                  have h : ((childHH (childLL (childLL (childLH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childLL (childLL (childLH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 0 (childLH (childLL (childLH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))
                (by
                  have h : ((childLL (childLH (childLL (childLH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childLH (childLL (childLH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                (by
                  have h : ((childLH (childLH (childLL (childLH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childLH (childLL (childLH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                (by
                  have h : ((childHL (childLH (childLL (childLH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childLH (childLL (childLH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                (by
                  have h : ((childHH (childLH (childLL (childLH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childLH (childLL (childLH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 0 (childHL (childLL (childLH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))
                (by
                  have h : ((childLL (childHL (childLL (childLH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childHL (childLL (childLH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                (by
                  have h : ((childLH (childHL (childLL (childLH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childHL (childLL (childLH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                (by
                  have h : ((childHL (childHL (childLL (childLH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childHL (childLL (childLH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                (by
                  have h : ((childHH (childHL (childLL (childLH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childHL (childLL (childLH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 0 (childHH (childLL (childLH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))
                (by
                  have h : ((childLL (childHH (childLL (childLH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childHH (childLL (childLH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                (by
                  have h : ((childLH (childHH (childLL (childLH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childHH (childLL (childLH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                (by
                  have h : ((childHL (childHH (childLL (childLH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childHH (childLL (childLH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                (by
                  have h : ((childHH (childHH (childLL (childLH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childHH (childLL (childLH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)))
        (by
          exact adaptiveCoverCheck_succ_of_children 1 (childLH (childLH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))
            (by
              exact adaptiveCoverCheck_succ_of_children 0 (childLL (childLH (childLH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))
                (by
                  have h : ((childLL (childLL (childLH (childLH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childLL (childLH (childLH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                (by
                  have h : ((childLH (childLL (childLH (childLH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childLL (childLH (childLH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                (by
                  have h : ((childHL (childLL (childLH (childLH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childLL (childLH (childLH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                (by
                  have h : ((childHH (childLL (childLH (childLH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childLL (childLH (childLH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 0 (childLH (childLH (childLH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))
                (by
                  have h : ((childLL (childLH (childLH (childLH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childLH (childLH (childLH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                (by
                  have h : ((childLH (childLH (childLH (childLH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childLH (childLH (childLH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                (by
                  have h : ((childHL (childLH (childLH (childLH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childLH (childLH (childLH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                (by
                  have h : ((childHH (childLH (childLH (childLH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childLH (childLH (childLH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 0 (childHL (childLH (childLH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))
                (by
                  have h : ((childLL (childHL (childLH (childLH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childHL (childLH (childLH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                (by
                  have h : ((childLH (childHL (childLH (childLH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childHL (childLH (childLH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                (by
                  have h : ((childHL (childHL (childLH (childLH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childHL (childLH (childLH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                (by
                  have h : ((childHH (childHL (childLH (childLH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childHL (childLH (childLH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 0 (childHH (childLH (childLH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))
                (by
                  have h : ((childLL (childHH (childLH (childLH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childHH (childLH (childLH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                (by
                  have h : ((childLH (childHH (childLH (childLH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childHH (childLH (childLH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                (by
                  have h : ((childHL (childHH (childLH (childLH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childHH (childLH (childLH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                (by
                  have h : ((childHH (childHH (childLH (childLH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childHH (childLH (childLH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)))
        (by
          exact adaptiveCoverCheck_succ_of_children 1 (childHL (childLH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))
            (by
              have h : ((childLL (childHL (childLH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHL (childLH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
            (by
              have h : ((childLH (childHL (childLH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHL (childLH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
            (by
              have h : ((childHL (childHL (childLH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHL (childLH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
            (by
              have h : ((childHH (childHL (childLH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHL (childLH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 1 (childHH (childLH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))
            (by
              have h : ((childLL (childHH (childLH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHH (childLH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
            (by
              have h : ((childLH (childHH (childLH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHH (childLH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
            (by
              have h : ((childHL (childHH (childLH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHH (childLH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
            (by
              have h : ((childHH (childHH (childLH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHH (childLH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childHL (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))
        (by
          have h : ((childLL (childHL (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL (childHL (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)
        (by
          have h : ((childLH (childHL (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH (childHL (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)
        (by
          have h : ((childHL (childHL (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL (childHL (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)
        (by
          have h : ((childHH (childHL (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH (childHL (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childHH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))
        (by
          have h : ((childLL (childHH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL (childHH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)
        (by
          have h : ((childLH (childHH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH (childHH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)
        (by
          have h : ((childHL (childHH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL (childHH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)
        (by
          have h : ((childHH (childHH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH (childHH (childLH (childHL (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h))

end PartE
end GerverSofa
