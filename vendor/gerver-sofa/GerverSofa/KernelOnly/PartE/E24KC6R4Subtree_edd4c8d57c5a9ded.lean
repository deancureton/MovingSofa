import GerverSofa.KernelOnly.PartE.E24KC2ProofHelpers

/-! KC6R4 explicit terminal-certificate subtree. No adaptive search. -/
noncomputable section

namespace GerverSofa
namespace PartE

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0000220021__c0__c0__c2__c1 :
    adaptiveCoverCheck 5 (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))
        (by
          have h : ((childLL (childLL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))) h)
        (by
          have h : ((childLH (childLL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))) h)
        (by
          exact adaptiveCoverCheck_succ_of_children 2 (childHL (childLL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))
            (by
              have h : ((childLL (childHL (childLL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 (childLL (childHL (childLL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
            (by
              have h : ((childLH (childHL (childLL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 (childLH (childHL (childLL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
            (by
              exact adaptiveCoverCheck_succ_of_children 1 (childHL (childHL (childLL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))
                (by
                  have h : ((childLL (childHL (childHL (childLL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHL (childHL (childLL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h)
                (by
                  have h : ((childLH (childHL (childHL (childLL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHL (childHL (childLL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h)
                (by
                  have h : ((childHL (childHL (childHL (childLL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHL (childHL (childLL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h)
                (by
                  have h : ((childHH (childHL (childHL (childLL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHL (childHL (childLL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 1 (childHH (childHL (childLL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))
                (by
                  have h : ((childLL (childHH (childHL (childLL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHH (childHL (childLL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h)
                (by
                  have h : ((childLH (childHH (childHL (childLL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHH (childHL (childLL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h)
                (by
                  have h : ((childHL (childHH (childHL (childLL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHH (childHL (childLL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h)
                (by
                  have h : ((childHH (childHH (childHL (childLL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHH (childHL (childLL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h)))
        (by
          exact adaptiveCoverCheck_succ_of_children 2 (childHH (childLL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))
            (by
              have h : ((childLL (childHH (childLL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 (childLL (childHH (childLL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
            (by
              have h : ((childLH (childHH (childLL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 (childLH (childHH (childLL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
            (by
              exact adaptiveCoverCheck_succ_of_children 1 (childHL (childHH (childLL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))
                (by
                  have h : ((childLL (childHL (childHH (childLL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHL (childHH (childLL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h)
                (by
                  have h : ((childLH (childHL (childHH (childLL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHL (childHH (childLL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h)
                (by
                  have h : ((childHL (childHL (childHH (childLL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHL (childHH (childLL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h)
                (by
                  have h : ((childHH (childHL (childHH (childLL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHL (childHH (childLL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 1 (childHH (childHH (childLL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))
                (by
                  have h : ((childLL (childHH (childHH (childLL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHH (childHH (childLL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h)
                (by
                  have h : ((childLH (childHH (childHH (childLL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHH (childHH (childLL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h)
                (by
                  have h : ((childHL (childHH (childHH (childLL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHH (childHH (childLL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h)
                (by
                  have h : ((childHH (childHH (childHH (childLL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHH (childHH (childLL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h))))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))
        (by
          have h : ((childLL (childLH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))) h)
        (by
          have h : ((childLH (childLH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))) h)
        (by
          exact adaptiveCoverCheck_succ_of_children 2 (childHL (childLH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))
            (by
              have h : ((childLL (childHL (childLH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 (childLL (childHL (childLH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
            (by
              have h : ((childLH (childHL (childLH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 (childLH (childHL (childLH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
            (by
              exact adaptiveCoverCheck_succ_of_children 1 (childHL (childHL (childLH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))
                (by
                  have h : ((childLL (childHL (childHL (childLH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHL (childHL (childLH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h)
                (by
                  have h : ((childLH (childHL (childHL (childLH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHL (childHL (childLH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h)
                (by
                  have h : ((childHL (childHL (childHL (childLH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHL (childHL (childLH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h)
                (by
                  have h : ((childHH (childHL (childHL (childLH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHL (childHL (childLH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 1 (childHH (childHL (childLH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))
                (by
                  have h : ((childLL (childHH (childHL (childLH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHH (childHL (childLH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h)
                (by
                  have h : ((childLH (childHH (childHL (childLH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHH (childHL (childLH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h)
                (by
                  have h : ((childHL (childHH (childHL (childLH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHH (childHL (childLH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h)
                (by
                  have h : ((childHH (childHH (childHL (childLH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHH (childHL (childLH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h)))
        (by
          exact adaptiveCoverCheck_succ_of_children 2 (childHH (childLH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))
            (by
              have h : ((childLL (childHH (childLH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 (childLL (childHH (childLH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
            (by
              have h : ((childLH (childHH (childLH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 (childLH (childHH (childLH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
            (by
              exact adaptiveCoverCheck_succ_of_children 1 (childHL (childHH (childLH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))
                (by
                  have h : ((childLL (childHL (childHH (childLH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHL (childHH (childLH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h)
                (by
                  have h : ((childLH (childHL (childHH (childLH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHL (childHH (childLH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h)
                (by
                  have h : ((childHL (childHL (childHH (childLH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHL (childHH (childLH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h)
                (by
                  have h : ((childHH (childHL (childHH (childLH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHL (childHH (childLH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 1 (childHH (childHH (childLH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))
                (by
                  have h : ((childLL (childHH (childHH (childLH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHH (childHH (childLH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h)
                (by
                  have h : ((childLH (childHH (childHH (childLH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHH (childHH (childLH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h)
                (by
                  have h : ((childHL (childHH (childHH (childLH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHH (childHH (childLH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h)
                (by
                  have h : ((childHH (childHH (childHH (childLH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHH (childHH (childLH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h))))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))
        (by
          exact adaptiveCoverCheck_succ_of_children 2 (childLL (childHL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))
            (by
              exact adaptiveCoverCheck_succ_of_children 1 (childLL (childLL (childHL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))
                (by
                  have h : ((childLL (childLL (childLL (childHL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childLL (childLL (childHL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h)
                (by
                  have h : ((childLH (childLL (childLL (childHL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childLL (childLL (childHL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h)
                (by
                  have h : ((childHL (childLL (childLL (childHL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childLL (childLL (childHL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h)
                (by
                  have h : ((childHH (childLL (childLL (childHL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childLL (childLL (childHL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 1 (childLH (childLL (childHL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))
                (by
                  have h : ((childLL (childLH (childLL (childHL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childLH (childLL (childHL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h)
                (by
                  have h : ((childLH (childLH (childLL (childHL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childLH (childLL (childHL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h)
                (by
                  have h : ((childHL (childLH (childLL (childHL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childLH (childLL (childHL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h)
                (by
                  have h : ((childHH (childLH (childLL (childHL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childLH (childLL (childHL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 1 (childHL (childLL (childHL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))
                (by
                  have h : ((childLL (childHL (childLL (childHL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHL (childLL (childHL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h)
                (by
                  have h : ((childLH (childHL (childLL (childHL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHL (childLL (childHL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h)
                (by
                  have h : ((childHL (childHL (childLL (childHL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHL (childLL (childHL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h)
                (by
                  have h : ((childHH (childHL (childLL (childHL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHL (childLL (childHL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 1 (childHH (childLL (childHL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))
                (by
                  have h : ((childLL (childHH (childLL (childHL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHH (childLL (childHL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h)
                (by
                  have h : ((childLH (childHH (childLL (childHL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHH (childLL (childHL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h)
                (by
                  have h : ((childHL (childHH (childLL (childHL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHH (childLL (childHL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h)
                (by
                  have h : ((childHH (childHH (childLL (childHL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHH (childLL (childHL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h)))
        (by
          exact adaptiveCoverCheck_succ_of_children 2 (childLH (childHL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))
            (by
              exact adaptiveCoverCheck_succ_of_children 1 (childLL (childLH (childHL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))
                (by
                  have h : ((childLL (childLL (childLH (childHL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childLL (childLH (childHL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h)
                (by
                  have h : ((childLH (childLL (childLH (childHL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childLL (childLH (childHL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h)
                (by
                  have h : ((childHL (childLL (childLH (childHL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childLL (childLH (childHL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h)
                (by
                  have h : ((childHH (childLL (childLH (childHL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childLL (childLH (childHL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 1 (childLH (childLH (childHL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))
                (by
                  have h : ((childLL (childLH (childLH (childHL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childLH (childLH (childHL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h)
                (by
                  have h : ((childLH (childLH (childLH (childHL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childLH (childLH (childHL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h)
                (by
                  have h : ((childHL (childLH (childLH (childHL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childLH (childLH (childHL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h)
                (by
                  have h : ((childHH (childLH (childLH (childHL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childLH (childLH (childHL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 1 (childHL (childLH (childHL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))
                (by
                  have h : ((childLL (childHL (childLH (childHL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHL (childLH (childHL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h)
                (by
                  have h : ((childLH (childHL (childLH (childHL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHL (childLH (childHL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h)
                (by
                  have h : ((childHL (childHL (childLH (childHL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHL (childLH (childHL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h)
                (by
                  have h : ((childHH (childHL (childLH (childHL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHL (childLH (childHL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 1 (childHH (childLH (childHL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))
                (by
                  have h : ((childLL (childHH (childLH (childHL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHH (childLH (childHL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h)
                (by
                  have h : ((childLH (childHH (childLH (childHL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHH (childLH (childHL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h)
                (by
                  have h : ((childHL (childHH (childLH (childHL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHH (childLH (childHL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h)
                (by
                  have h : ((childHH (childHH (childLH (childHL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHH (childLH (childHL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h)))
        (by
          exact adaptiveCoverCheck_succ_of_children 2 (childHL (childHL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))
            (by
              have h : ((childLL (childHL (childHL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 (childLL (childHL (childHL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
            (by
              have h : ((childLH (childHL (childHL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 (childLH (childHL (childHL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
            (by
              have h : ((childHL (childHL (childHL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 (childHL (childHL (childHL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
            (by
              have h : ((childHH (childHL (childHL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 (childHH (childHL (childHL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 2 (childHH (childHL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))
            (by
              have h : ((childLL (childHH (childHL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 (childLL (childHH (childHL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
            (by
              have h : ((childLH (childHH (childHL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 (childLH (childHH (childHL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
            (by
              have h : ((childHL (childHH (childHL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 (childHL (childHH (childHL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
            (by
              have h : ((childHH (childHH (childHL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 (childHH (childHH (childHL (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))
        (by
          exact adaptiveCoverCheck_succ_of_children 2 (childLL (childHH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))
            (by
              exact adaptiveCoverCheck_succ_of_children 1 (childLL (childLL (childHH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))
                (by
                  have h : ((childLL (childLL (childLL (childHH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childLL (childLL (childHH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h)
                (by
                  have h : ((childLH (childLL (childLL (childHH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childLL (childLL (childHH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h)
                (by
                  have h : ((childHL (childLL (childLL (childHH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childLL (childLL (childHH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h)
                (by
                  have h : ((childHH (childLL (childLL (childHH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childLL (childLL (childHH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 1 (childLH (childLL (childHH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))
                (by
                  have h : ((childLL (childLH (childLL (childHH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childLH (childLL (childHH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h)
                (by
                  have h : ((childLH (childLH (childLL (childHH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childLH (childLL (childHH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h)
                (by
                  have h : ((childHL (childLH (childLL (childHH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childLH (childLL (childHH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h)
                (by
                  have h : ((childHH (childLH (childLL (childHH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childLH (childLL (childHH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 1 (childHL (childLL (childHH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))
                (by
                  have h : ((childLL (childHL (childLL (childHH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHL (childLL (childHH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h)
                (by
                  have h : ((childLH (childHL (childLL (childHH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHL (childLL (childHH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h)
                (by
                  have h : ((childHL (childHL (childLL (childHH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHL (childLL (childHH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h)
                (by
                  have h : ((childHH (childHL (childLL (childHH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHL (childLL (childHH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 1 (childHH (childLL (childHH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))
                (by
                  have h : ((childLL (childHH (childLL (childHH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHH (childLL (childHH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h)
                (by
                  have h : ((childLH (childHH (childLL (childHH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHH (childLL (childHH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h)
                (by
                  have h : ((childHL (childHH (childLL (childHH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHH (childLL (childHH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h)
                (by
                  have h : ((childHH (childHH (childLL (childHH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHH (childLL (childHH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h)))
        (by
          exact adaptiveCoverCheck_succ_of_children 2 (childLH (childHH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))
            (by
              exact adaptiveCoverCheck_succ_of_children 1 (childLL (childLH (childHH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))
                (by
                  have h : ((childLL (childLL (childLH (childHH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childLL (childLH (childHH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h)
                (by
                  have h : ((childLH (childLL (childLH (childHH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childLL (childLH (childHH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h)
                (by
                  have h : ((childHL (childLL (childLH (childHH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childLL (childLH (childHH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h)
                (by
                  have h : ((childHH (childLL (childLH (childHH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childLL (childLH (childHH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 1 (childLH (childLH (childHH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))
                (by
                  have h : ((childLL (childLH (childLH (childHH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childLH (childLH (childHH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h)
                (by
                  have h : ((childLH (childLH (childLH (childHH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childLH (childLH (childHH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h)
                (by
                  have h : ((childHL (childLH (childLH (childHH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childLH (childLH (childHH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h)
                (by
                  have h : ((childHH (childLH (childLH (childHH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childLH (childLH (childHH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 1 (childHL (childLH (childHH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))
                (by
                  have h : ((childLL (childHL (childLH (childHH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHL (childLH (childHH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h)
                (by
                  have h : ((childLH (childHL (childLH (childHH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHL (childLH (childHH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h)
                (by
                  have h : ((childHL (childHL (childLH (childHH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHL (childLH (childHH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h)
                (by
                  have h : ((childHH (childHL (childLH (childHH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHL (childLH (childHH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 1 (childHH (childLH (childHH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))
                (by
                  have h : ((childLL (childHH (childLH (childHH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHH (childLH (childHH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h)
                (by
                  have h : ((childLH (childHH (childLH (childHH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHH (childLH (childHH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h)
                (by
                  have h : ((childHL (childHH (childLH (childHH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHH (childLH (childHH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h)
                (by
                  have h : ((childHH (childHH (childLH (childHH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHH (childLH (childHH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))) h)))
        (by
          exact adaptiveCoverCheck_succ_of_children 2 (childHL (childHH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))
            (by
              have h : ((childLL (childHL (childHH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 (childLL (childHL (childHH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
            (by
              have h : ((childLH (childHL (childHH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 (childLH (childHL (childHH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
            (by
              have h : ((childHL (childHL (childHH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 (childHL (childHL (childHH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
            (by
              have h : ((childHH (childHL (childHH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 (childHH (childHL (childHH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 2 (childHH (childHH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))
            (by
              have h : ((childLL (childHH (childHH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 (childLL (childHH (childHH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
            (by
              have h : ((childLH (childHH (childHH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 (childLH (childHH (childHH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
            (by
              have h : ((childHL (childHH (childHH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 (childHL (childHH (childHH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
            (by
              have h : ((childHH (childHH (childHH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 (childHH (childHH (childHH (childLH (childHL (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)))

end PartE
end GerverSofa
