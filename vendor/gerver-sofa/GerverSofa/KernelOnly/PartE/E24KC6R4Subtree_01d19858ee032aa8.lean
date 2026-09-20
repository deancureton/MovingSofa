import GerverSofa.KernelOnly.PartE.E24KC2ProofHelpers

/-! KC6R4 explicit terminal-certificate subtree. No adaptive search. -/
noncomputable section

namespace GerverSofa
namespace PartE

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111133113__c0__c1__c0 :
    adaptiveCoverCheck 6 (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))
        (by
          exact adaptiveCoverCheck_succ_of_children 3 (childLL (childLL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))
            (by
              have h : ((childLL (childLL (childLL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLL (childLL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))) h)
            (by
              have h : ((childLH (childLL (childLL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLL (childLL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))) h)
            (by
              have h : ((childHL (childLL (childLL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childLL (childLL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))) h)
            (by
              have h : ((childHH (childLL (childLL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childLL (childLL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 3 (childLH (childLL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))
            (by
              have h : ((childLL (childLH (childLL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLH (childLL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))) h)
            (by
              have h : ((childLH (childLH (childLL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLH (childLL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))) h)
            (by
              have h : ((childHL (childLH (childLL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childLH (childLL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))) h)
            (by
              have h : ((childHH (childLH (childLL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childLH (childLL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))
            (by
              have h : ((childLL (childHL (childLL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childHL (childLL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))) h)
            (by
              exact adaptiveCoverCheck_succ_of_children 2 (childLH (childHL (childLL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))
                (by
                  have h : ((childLL (childLH (childHL (childLL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLL (childLH (childHL (childLL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)
                (by
                  have h : ((childLH (childLH (childHL (childLL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLH (childLH (childHL (childLL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)
                (by
                  have h : ((childHL (childLH (childHL (childLL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHL (childLH (childHL (childLL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)
                (by
                  have h : ((childHH (childLH (childHL (childLL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHH (childLH (childHL (childLL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 2 (childHL (childHL (childLL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))
                (by
                  have h : ((childLL (childHL (childHL (childLL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLL (childHL (childHL (childLL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)
                (by
                  have h : ((childLH (childHL (childHL (childLL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLH (childHL (childHL (childLL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)
                (by
                  have h : ((childHL (childHL (childHL (childLL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHL (childHL (childHL (childLL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)
                (by
                  have h : ((childHH (childHL (childHL (childLL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHH (childHL (childHL (childLL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 2 (childHH (childHL (childLL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))
                (by
                  have h : ((childLL (childHH (childHL (childLL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLL (childHH (childHL (childLL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)
                (by
                  have h : ((childLH (childHH (childHL (childLL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLH (childHH (childHL (childLL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)
                (by
                  have h : ((childHL (childHH (childHL (childLL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHL (childHH (childHL (childLL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)
                (by
                  have h : ((childHH (childHH (childHL (childLL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHH (childHH (childHL (childLL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)))
        (by
          exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))
            (by
              exact adaptiveCoverCheck_succ_of_children 2 (childLL (childHH (childLL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))
                (by
                  have h : ((childLL (childLL (childHH (childLL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLL (childLL (childHH (childLL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)
                (by
                  have h : ((childLH (childLL (childHH (childLL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLH (childLL (childHH (childLL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)
                (by
                  have h : ((childHL (childLL (childHH (childLL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHL (childLL (childHH (childLL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)
                (by
                  have h : ((childHH (childLL (childHH (childLL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHH (childLL (childHH (childLL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 2 (childLH (childHH (childLL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))
                (by
                  have h : ((childLL (childLH (childHH (childLL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLL (childLH (childHH (childLL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)
                (by
                  have h : ((childLH (childLH (childHH (childLL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLH (childLH (childHH (childLL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)
                (by
                  have h : ((childHL (childLH (childHH (childLL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHL (childLH (childHH (childLL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)
                (by
                  have h : ((childHH (childLH (childHH (childLL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHH (childLH (childHH (childLL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 2 (childHL (childHH (childLL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))
                (by
                  have h : ((childLL (childHL (childHH (childLL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLL (childHL (childHH (childLL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)
                (by
                  have h : ((childLH (childHL (childHH (childLL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLH (childHL (childHH (childLL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)
                (by
                  have h : ((childHL (childHL (childHH (childLL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHL (childHL (childHH (childLL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)
                (by
                  have h : ((childHH (childHL (childHH (childLL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHH (childHL (childHH (childLL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 2 (childHH (childHH (childLL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))
                (by
                  have h : ((childLL (childHH (childHH (childLL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLL (childHH (childHH (childLL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)
                (by
                  have h : ((childLH (childHH (childHH (childLL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLH (childHH (childHH (childLL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)
                (by
                  have h : ((childHL (childHH (childHH (childLL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHL (childHH (childHH (childLL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)
                (by
                  have h : ((childHH (childHH (childHH (childLL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHH (childHH (childHH (childLL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h))))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))
        (by
          exact adaptiveCoverCheck_succ_of_children 3 (childLL (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))
            (by
              have h : ((childLL (childLL (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLL (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))) h)
            (by
              have h : ((childLH (childLL (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLL (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))) h)
            (by
              exact adaptiveCoverCheck_succ_of_children 2 (childHL (childLL (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))
                (by
                  have h : ((childLL (childHL (childLL (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLL (childHL (childLL (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)
                (by
                  have h : ((childLH (childHL (childLL (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLH (childHL (childLL (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)
                (by
                  have h : ((childHL (childHL (childLL (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHL (childHL (childLL (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)
                (by
                  have h : ((childHH (childHL (childLL (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHH (childHL (childLL (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 2 (childHH (childLL (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))
                (by
                  have h : ((childLL (childHH (childLL (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLL (childHH (childLL (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)
                (by
                  have h : ((childLH (childHH (childLL (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLH (childHH (childLL (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)
                (by
                  have h : ((childHL (childHH (childLL (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHL (childHH (childLL (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)
                (by
                  have h : ((childHH (childHH (childLL (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHH (childHH (childLL (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)))
        (by
          exact adaptiveCoverCheck_succ_of_children 3 (childLH (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))
            (by
              have h : ((childLL (childLH (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLH (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))) h)
            (by
              have h : ((childLH (childLH (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLH (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))) h)
            (by
              exact adaptiveCoverCheck_succ_of_children 2 (childHL (childLH (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))
                (by
                  have h : ((childLL (childHL (childLH (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLL (childHL (childLH (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)
                (by
                  have h : ((childLH (childHL (childLH (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLH (childHL (childLH (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)
                (by
                  have h : ((childHL (childHL (childLH (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHL (childHL (childLH (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)
                (by
                  have h : ((childHH (childHL (childLH (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHH (childHL (childLH (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 2 (childHH (childLH (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))
                (by
                  have h : ((childLL (childHH (childLH (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLL (childHH (childLH (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)
                (by
                  have h : ((childLH (childHH (childLH (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLH (childHH (childLH (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)
                (by
                  have h : ((childHL (childHH (childLH (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHL (childHH (childLH (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)
                (by
                  have h : ((childHH (childHH (childLH (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHH (childHH (childLH (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)))
        (by
          exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))
            (by
              exact adaptiveCoverCheck_succ_of_children 2 (childLL (childHL (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))
                (by
                  have h : ((childLL (childLL (childHL (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLL (childLL (childHL (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)
                (by
                  have h : ((childLH (childLL (childHL (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLH (childLL (childHL (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)
                (by
                  have h : ((childHL (childLL (childHL (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHL (childLL (childHL (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)
                (by
                  have h : ((childHH (childLL (childHL (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHH (childLL (childHL (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 2 (childLH (childHL (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))
                (by
                  have h : ((childLL (childLH (childHL (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLL (childLH (childHL (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)
                (by
                  have h : ((childLH (childLH (childHL (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLH (childLH (childHL (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)
                (by
                  have h : ((childHL (childLH (childHL (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHL (childLH (childHL (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)
                (by
                  have h : ((childHH (childLH (childHL (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHH (childLH (childHL (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 2 (childHL (childHL (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))
                (by
                  have h : ((childLL (childHL (childHL (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLL (childHL (childHL (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)
                (by
                  have h : ((childLH (childHL (childHL (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLH (childHL (childHL (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)
                (by
                  have h : ((childHL (childHL (childHL (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHL (childHL (childHL (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)
                (by
                  have h : ((childHH (childHL (childHL (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHH (childHL (childHL (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 2 (childHH (childHL (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))
                (by
                  have h : ((childLL (childHH (childHL (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLL (childHH (childHL (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)
                (by
                  have h : ((childLH (childHH (childHL (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLH (childHH (childHL (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)
                (by
                  have h : ((childHL (childHH (childHL (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHL (childHH (childHL (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)
                (by
                  have h : ((childHH (childHH (childHL (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHH (childHH (childHL (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)))
        (by
          exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))
            (by
              exact adaptiveCoverCheck_succ_of_children 2 (childLL (childHH (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))
                (by
                  have h : ((childLL (childLL (childHH (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLL (childLL (childHH (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)
                (by
                  have h : ((childLH (childLL (childHH (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLH (childLL (childHH (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)
                (by
                  have h : ((childHL (childLL (childHH (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHL (childLL (childHH (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)
                (by
                  have h : ((childHH (childLL (childHH (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHH (childLL (childHH (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 2 (childLH (childHH (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))
                (by
                  have h : ((childLL (childLH (childHH (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLL (childLH (childHH (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)
                (by
                  have h : ((childLH (childLH (childHH (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLH (childLH (childHH (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)
                (by
                  have h : ((childHL (childLH (childHH (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHL (childLH (childHH (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)
                (by
                  have h : ((childHH (childLH (childHH (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHH (childLH (childHH (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 2 (childHL (childHH (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))
                (by
                  have h : ((childLL (childHL (childHH (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLL (childHL (childHH (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)
                (by
                  have h : ((childLH (childHL (childHH (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLH (childHL (childHH (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)
                (by
                  have h : ((childHL (childHL (childHH (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHL (childHL (childHH (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)
                (by
                  have h : ((childHH (childHL (childHH (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHH (childHL (childHH (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 2 (childHH (childHH (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))
                (by
                  have h : ((childLL (childHH (childHH (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLL (childHH (childHH (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)
                (by
                  have h : ((childLH (childHH (childHH (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLH (childHH (childHH (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)
                (by
                  have h : ((childHL (childHH (childHH (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHL (childHH (childHH (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)
                (by
                  have h : ((childHH (childHH (childHH (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHH (childHH (childHH (childLH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h))))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))
        (by
          exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))
            (by
              have h : ((childLL (childLL (childHL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLL (childHL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))) h)
            (by
              have h : ((childLH (childLL (childHL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLL (childHL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))) h)
            (by
              have h : ((childHL (childLL (childHL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childLL (childHL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))) h)
            (by
              have h : ((childHH (childLL (childHL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childLL (childHL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))
            (by
              have h : ((childLL (childLH (childHL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLH (childHL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))) h)
            (by
              have h : ((childLH (childLH (childHL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLH (childHL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))) h)
            (by
              have h : ((childHL (childLH (childHL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childLH (childHL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))) h)
            (by
              have h : ((childHH (childLH (childHL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childLH (childHL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))) h))
        (by
          have h : ((childHL (childHL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
        (by
          have h : ((childHH (childHL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))
        (by
          exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))
            (by
              have h : ((childLL (childLL (childHH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLL (childHH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))) h)
            (by
              have h : ((childLH (childLL (childHH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLL (childHH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))) h)
            (by
              have h : ((childHL (childLL (childHH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childLL (childHH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))) h)
            (by
              have h : ((childHH (childLL (childHH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childLL (childHH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))
            (by
              have h : ((childLL (childLH (childHH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLH (childHH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))) h)
            (by
              have h : ((childLH (childLH (childHH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLH (childHH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))) h)
            (by
              have h : ((childHL (childLH (childHH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childLH (childHH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))) h)
            (by
              have h : ((childHH (childLH (childHH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childLH (childHH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))) h))
        (by
          have h : ((childHL (childHH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
        (by
          have h : ((childHH (childHH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h))

end PartE
end GerverSofa
