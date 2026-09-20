import GerverSofa.KernelOnly.PartE.E24KC2ProofHelpers

/-! KC6R4 explicit terminal-certificate subtree. No adaptive search. -/
noncomputable section

namespace GerverSofa
namespace PartE

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111133113__c1__c1__c0__c2 :
    adaptiveCoverCheck 5 (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))
        (by
          exact adaptiveCoverCheck_succ_of_children 2 (childLL (childLL (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))
            (by
              exact adaptiveCoverCheck_succ_of_children 1 (childLL (childLL (childLL (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))
                (by
                  have h : ((childLL (childLL (childLL (childLL (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childLL (childLL (childLL (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
                (by
                  have h : ((childLH (childLL (childLL (childLL (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childLL (childLL (childLL (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
                (by
                  have h : ((childHL (childLL (childLL (childLL (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childLL (childLL (childLL (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
                (by
                  have h : ((childHH (childLL (childLL (childLL (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childLL (childLL (childLL (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 1 (childLH (childLL (childLL (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))
                (by
                  have h : ((childLL (childLH (childLL (childLL (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childLH (childLL (childLL (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
                (by
                  have h : ((childLH (childLH (childLL (childLL (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childLH (childLL (childLL (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
                (by
                  have h : ((childHL (childLH (childLL (childLL (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childLH (childLL (childLL (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
                (by
                  have h : ((childHH (childLH (childLL (childLL (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childLH (childLL (childLL (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h))
            (by
              have h : ((childHL (childLL (childLL (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 (childHL (childLL (childLL (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)
            (by
              have h : ((childHH (childLL (childLL (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 (childHH (childLL (childLL (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 2 (childLH (childLL (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))
            (by
              exact adaptiveCoverCheck_succ_of_children 1 (childLL (childLH (childLL (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))
                (by
                  have h : ((childLL (childLL (childLH (childLL (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childLL (childLH (childLL (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
                (by
                  have h : ((childLH (childLL (childLH (childLL (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childLL (childLH (childLL (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
                (by
                  have h : ((childHL (childLL (childLH (childLL (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childLL (childLH (childLL (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
                (by
                  have h : ((childHH (childLL (childLH (childLL (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childLL (childLH (childLL (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 1 (childLH (childLH (childLL (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))
                (by
                  have h : ((childLL (childLH (childLH (childLL (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childLH (childLH (childLL (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
                (by
                  have h : ((childLH (childLH (childLH (childLL (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childLH (childLH (childLL (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
                (by
                  have h : ((childHL (childLH (childLH (childLL (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childLH (childLH (childLL (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
                (by
                  have h : ((childHH (childLH (childLH (childLL (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childLH (childLH (childLL (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h))
            (by
              have h : ((childHL (childLH (childLL (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 (childHL (childLH (childLL (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)
            (by
              have h : ((childHH (childLH (childLL (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 (childHH (childLH (childLL (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h))
        (by
          have h : ((childHL (childLL (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childLL (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))) h)
        (by
          have h : ((childHH (childLL (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childLL (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))
        (by
          exact adaptiveCoverCheck_succ_of_children 2 (childLL (childLH (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))
            (by
              exact adaptiveCoverCheck_succ_of_children 1 (childLL (childLL (childLH (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))
                (by
                  have h : ((childLL (childLL (childLL (childLH (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childLL (childLL (childLH (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
                (by
                  have h : ((childLH (childLL (childLL (childLH (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childLL (childLL (childLH (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
                (by
                  have h : ((childHL (childLL (childLL (childLH (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childLL (childLL (childLH (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
                (by
                  have h : ((childHH (childLL (childLL (childLH (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childLL (childLL (childLH (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 1 (childLH (childLL (childLH (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))
                (by
                  have h : ((childLL (childLH (childLL (childLH (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childLH (childLL (childLH (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
                (by
                  have h : ((childLH (childLH (childLL (childLH (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childLH (childLL (childLH (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
                (by
                  have h : ((childHL (childLH (childLL (childLH (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childLH (childLL (childLH (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
                (by
                  have h : ((childHH (childLH (childLL (childLH (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childLH (childLL (childLH (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h))
            (by
              have h : ((childHL (childLL (childLH (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 (childHL (childLL (childLH (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)
            (by
              have h : ((childHH (childLL (childLH (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 (childHH (childLL (childLH (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 2 (childLH (childLH (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))
            (by
              exact adaptiveCoverCheck_succ_of_children 1 (childLL (childLH (childLH (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))
                (by
                  have h : ((childLL (childLL (childLH (childLH (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childLL (childLH (childLH (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
                (by
                  have h : ((childLH (childLL (childLH (childLH (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childLL (childLH (childLH (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
                (by
                  have h : ((childHL (childLL (childLH (childLH (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childLL (childLH (childLH (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
                (by
                  have h : ((childHH (childLL (childLH (childLH (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childLL (childLH (childLH (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 1 (childLH (childLH (childLH (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))
                (by
                  have h : ((childLL (childLH (childLH (childLH (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childLH (childLH (childLH (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
                (by
                  have h : ((childLH (childLH (childLH (childLH (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childLH (childLH (childLH (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
                (by
                  have h : ((childHL (childLH (childLH (childLH (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childLH (childLH (childLH (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
                (by
                  have h : ((childHH (childLH (childLH (childLH (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childLH (childLH (childLH (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h))
            (by
              have h : ((childHL (childLH (childLH (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 (childHL (childLH (childLH (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)
            (by
              have h : ((childHH (childLH (childLH (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 (childHH (childLH (childLH (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h))
        (by
          have h : ((childHL (childLH (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childLH (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))) h)
        (by
          have h : ((childHH (childLH (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childLH (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))) h))
    (by
      have h : ((childHL (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
    (by
      have h : ((childHH (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)

end PartE
end GerverSofa
