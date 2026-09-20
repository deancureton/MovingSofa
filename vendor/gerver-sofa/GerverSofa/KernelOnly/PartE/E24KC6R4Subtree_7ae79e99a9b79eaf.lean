import GerverSofa.KernelOnly.PartE.E24KC2ProofHelpers

/-! KC6R4 explicit terminal-certificate subtree. No adaptive search. -/
noncomputable section

namespace GerverSofa
namespace PartE

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111133113__c1__c1__c0__c0 :
    adaptiveCoverCheck 5 (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))
        (by
          have h : ((childLL (childLL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))) h)
        (by
          have h : ((childLH (childLL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))) h)
        (by
          have h : ((childHL (childLL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childLL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))) h)
        (by
          have h : ((childHH (childLL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childLL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))
        (by
          have h : ((childLL (childLH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))) h)
        (by
          have h : ((childLH (childLH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))) h)
        (by
          have h : ((childHL (childLH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childLH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))) h)
        (by
          have h : ((childHH (childLH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childLH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))
        (by
          exact adaptiveCoverCheck_succ_of_children 2 (childLL (childHL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))
            (by
              have h : ((childLL (childLL (childHL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 (childLL (childLL (childHL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)
            (by
              have h : ((childLH (childLL (childHL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 (childLH (childLL (childHL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)
            (by
              have h : ((childHL (childLL (childHL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 (childHL (childLL (childHL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)
            (by
              have h : ((childHH (childLL (childHL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 (childHH (childLL (childHL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 2 (childLH (childHL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))
            (by
              have h : ((childLL (childLH (childHL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 (childLL (childLH (childHL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)
            (by
              have h : ((childLH (childLH (childHL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 (childLH (childLH (childHL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)
            (by
              have h : ((childHL (childLH (childHL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 (childHL (childLH (childHL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)
            (by
              have h : ((childHH (childLH (childHL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 (childHH (childLH (childHL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 2 (childHL (childHL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))
            (by
              exact adaptiveCoverCheck_succ_of_children 1 (childLL (childHL (childHL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))
                (by
                  have h : ((childLL (childLL (childHL (childHL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childLL (childHL (childHL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
                (by
                  have h : ((childLH (childLL (childHL (childHL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childLL (childHL (childHL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
                (by
                  have h : ((childHL (childLL (childHL (childHL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childLL (childHL (childHL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
                (by
                  have h : ((childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 1 (childLH (childHL (childHL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))
                (by
                  have h : ((childLL (childLH (childHL (childHL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childLH (childHL (childHL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
                (by
                  have h : ((childLH (childLH (childHL (childHL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childLH (childHL (childHL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
                (by
                  have h : ((childHL (childLH (childHL (childHL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childLH (childHL (childHL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
                (by
                  have h : ((childHH (childLH (childHL (childHL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childLH (childHL (childHL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 1 (childHL (childHL (childHL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))
                (by
                  have h : ((childLL (childHL (childHL (childHL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHL (childHL (childHL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
                (by
                  have h : ((childLH (childHL (childHL (childHL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHL (childHL (childHL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
                (by
                  have h : ((childHL (childHL (childHL (childHL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHL (childHL (childHL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
                (by
                  have h : ((childHH (childHL (childHL (childHL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHL (childHL (childHL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 1 (childHH (childHL (childHL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))
                (by
                  have h : ((childLL (childHH (childHL (childHL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHH (childHL (childHL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
                (by
                  have h : ((childLH (childHH (childHL (childHL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHH (childHL (childHL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
                (by
                  have h : ((childHL (childHH (childHL (childHL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHH (childHL (childHL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
                (by
                  have h : ((childHH (childHH (childHL (childHL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHH (childHL (childHL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)))
        (by
          exact adaptiveCoverCheck_succ_of_children 2 (childHH (childHL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))
            (by
              exact adaptiveCoverCheck_succ_of_children 1 (childLL (childHH (childHL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))
                (by
                  have h : ((childLL (childLL (childHH (childHL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childLL (childHH (childHL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
                (by
                  have h : ((childLH (childLL (childHH (childHL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childLL (childHH (childHL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
                (by
                  have h : ((childHL (childLL (childHH (childHL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childLL (childHH (childHL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
                (by
                  have h : ((childHH (childLL (childHH (childHL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childLL (childHH (childHL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 1 (childLH (childHH (childHL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))
                (by
                  have h : ((childLL (childLH (childHH (childHL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childLH (childHH (childHL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
                (by
                  have h : ((childLH (childLH (childHH (childHL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childLH (childHH (childHL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
                (by
                  have h : ((childHL (childLH (childHH (childHL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childLH (childHH (childHL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
                (by
                  have h : ((childHH (childLH (childHH (childHL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childLH (childHH (childHL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 1 (childHL (childHH (childHL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))
                (by
                  have h : ((childLL (childHL (childHH (childHL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHL (childHH (childHL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
                (by
                  have h : ((childLH (childHL (childHH (childHL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHL (childHH (childHL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
                (by
                  have h : ((childHL (childHL (childHH (childHL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHL (childHH (childHL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
                (by
                  have h : ((childHH (childHL (childHH (childHL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHL (childHH (childHL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 1 (childHH (childHH (childHL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))
                (by
                  have h : ((childLL (childHH (childHH (childHL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHH (childHH (childHL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
                (by
                  have h : ((childLH (childHH (childHH (childHL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHH (childHH (childHL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
                (by
                  have h : ((childHL (childHH (childHH (childHL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHH (childHH (childHL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
                (by
                  have h : ((childHH (childHH (childHH (childHL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHH (childHH (childHL (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h))))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))
        (by
          exact adaptiveCoverCheck_succ_of_children 2 (childLL (childHH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))
            (by
              have h : ((childLL (childLL (childHH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 (childLL (childLL (childHH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)
            (by
              have h : ((childLH (childLL (childHH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 (childLH (childLL (childHH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)
            (by
              have h : ((childHL (childLL (childHH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 (childHL (childLL (childHH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)
            (by
              have h : ((childHH (childLL (childHH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 (childHH (childLL (childHH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 2 (childLH (childHH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))
            (by
              have h : ((childLL (childLH (childHH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 (childLL (childLH (childHH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)
            (by
              have h : ((childLH (childLH (childHH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 (childLH (childLH (childHH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)
            (by
              have h : ((childHL (childLH (childHH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 (childHL (childLH (childHH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)
            (by
              have h : ((childHH (childLH (childHH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 (childHH (childLH (childHH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 2 (childHL (childHH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))
            (by
              exact adaptiveCoverCheck_succ_of_children 1 (childLL (childHL (childHH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))
                (by
                  have h : ((childLL (childLL (childHL (childHH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childLL (childHL (childHH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
                (by
                  have h : ((childLH (childLL (childHL (childHH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childLL (childHL (childHH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
                (by
                  have h : ((childHL (childLL (childHL (childHH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childLL (childHL (childHH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
                (by
                  have h : ((childHH (childLL (childHL (childHH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childLL (childHL (childHH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 1 (childLH (childHL (childHH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))
                (by
                  have h : ((childLL (childLH (childHL (childHH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childLH (childHL (childHH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
                (by
                  have h : ((childLH (childLH (childHL (childHH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childLH (childHL (childHH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
                (by
                  have h : ((childHL (childLH (childHL (childHH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childLH (childHL (childHH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
                (by
                  have h : ((childHH (childLH (childHL (childHH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childLH (childHL (childHH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 1 (childHL (childHL (childHH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))
                (by
                  have h : ((childLL (childHL (childHL (childHH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHL (childHL (childHH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
                (by
                  have h : ((childLH (childHL (childHL (childHH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHL (childHL (childHH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
                (by
                  have h : ((childHL (childHL (childHL (childHH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHL (childHL (childHH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
                (by
                  have h : ((childHH (childHL (childHL (childHH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHL (childHL (childHH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 1 (childHH (childHL (childHH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))
                (by
                  have h : ((childLL (childHH (childHL (childHH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHH (childHL (childHH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
                (by
                  have h : ((childLH (childHH (childHL (childHH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHH (childHL (childHH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
                (by
                  have h : ((childHL (childHH (childHL (childHH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHH (childHL (childHH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
                (by
                  have h : ((childHH (childHH (childHL (childHH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHH (childHL (childHH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)))
        (by
          exact adaptiveCoverCheck_succ_of_children 2 (childHH (childHH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))
            (by
              exact adaptiveCoverCheck_succ_of_children 1 (childLL (childHH (childHH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))
                (by
                  have h : ((childLL (childLL (childHH (childHH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childLL (childHH (childHH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
                (by
                  have h : ((childLH (childLL (childHH (childHH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childLL (childHH (childHH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
                (by
                  have h : ((childHL (childLL (childHH (childHH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childLL (childHH (childHH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
                (by
                  have h : ((childHH (childLL (childHH (childHH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childLL (childHH (childHH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 1 (childLH (childHH (childHH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))
                (by
                  have h : ((childLL (childLH (childHH (childHH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childLH (childHH (childHH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
                (by
                  have h : ((childLH (childLH (childHH (childHH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childLH (childHH (childHH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
                (by
                  have h : ((childHL (childLH (childHH (childHH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childLH (childHH (childHH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
                (by
                  have h : ((childHH (childLH (childHH (childHH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childLH (childHH (childHH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 1 (childHL (childHH (childHH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))
                (by
                  have h : ((childLL (childHL (childHH (childHH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHL (childHH (childHH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
                (by
                  have h : ((childLH (childHL (childHH (childHH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHL (childHH (childHH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
                (by
                  have h : ((childHL (childHL (childHH (childHH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHL (childHH (childHH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
                (by
                  have h : ((childHH (childHL (childHH (childHH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHL (childHH (childHH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 1 (childHH (childHH (childHH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))
                (by
                  have h : ((childLL (childHH (childHH (childHH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHH (childHH (childHH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
                (by
                  have h : ((childLH (childHH (childHH (childHH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHH (childHH (childHH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
                (by
                  have h : ((childHL (childHH (childHH (childHH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHH (childHH (childHH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
                (by
                  have h : ((childHH (childHH (childHH (childHH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHH (childHH (childHH (childLL (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h))))

end PartE
end GerverSofa
