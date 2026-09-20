import GerverSofa.KernelOnly.PartE.E24KC2ProofHelpers

/-! KC6R4 explicit terminal-certificate subtree. No adaptive search. -/
noncomputable section

namespace GerverSofa
namespace PartE

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0000220021__c1__c0__c3 :
    adaptiveCoverCheck 6 (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))
        (by
          exact adaptiveCoverCheck_succ_of_children 3 (childLL (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))
            (by
              have h : ((childLL (childLL (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLL (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))) h)
            (by
              have h : ((childLH (childLL (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLL (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))) h)
            (by
              exact adaptiveCoverCheck_succ_of_children 2 (childHL (childLL (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))
                (by
                  have h : ((childLL (childHL (childLL (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLL (childHL (childLL (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childLH (childHL (childLL (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLH (childHL (childLL (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHL (childHL (childLL (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHL (childHL (childLL (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHH (childHL (childLL (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHH (childHL (childLL (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 2 (childHH (childLL (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))
                (by
                  have h : ((childLL (childHH (childLL (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLL (childHH (childLL (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childLH (childHH (childLL (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLH (childHH (childLL (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHL (childHH (childLL (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHL (childHH (childLL (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHH (childHH (childLL (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHH (childHH (childLL (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)))
        (by
          exact adaptiveCoverCheck_succ_of_children 3 (childLH (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))
            (by
              have h : ((childLL (childLH (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLH (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))) h)
            (by
              have h : ((childLH (childLH (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLH (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))) h)
            (by
              exact adaptiveCoverCheck_succ_of_children 2 (childHL (childLH (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))
                (by
                  have h : ((childLL (childHL (childLH (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLL (childHL (childLH (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childLH (childHL (childLH (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLH (childHL (childLH (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHL (childHL (childLH (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHL (childHL (childLH (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHH (childHL (childLH (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHH (childHL (childLH (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 2 (childHH (childLH (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))
                (by
                  have h : ((childLL (childHH (childLH (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLL (childHH (childLH (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childLH (childHH (childLH (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLH (childHH (childLH (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHL (childHH (childLH (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHL (childHH (childLH (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHH (childHH (childLH (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHH (childHH (childLH (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)))
        (by
          exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))
            (by
              exact adaptiveCoverCheck_succ_of_children 2 (childLL (childHL (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))
                (by
                  have h : ((childLL (childLL (childHL (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLL (childLL (childHL (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childLH (childLL (childHL (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLH (childLL (childHL (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHL (childLL (childHL (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHL (childLL (childHL (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHH (childLL (childHL (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHH (childLL (childHL (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 2 (childLH (childHL (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))
                (by
                  have h : ((childLL (childLH (childHL (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLL (childLH (childHL (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childLH (childLH (childHL (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLH (childLH (childHL (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHL (childLH (childHL (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHL (childLH (childHL (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHH (childLH (childHL (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHH (childLH (childHL (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 2 (childHL (childHL (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))
                (by
                  have h : ((childLL (childHL (childHL (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLL (childHL (childHL (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childLH (childHL (childHL (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLH (childHL (childHL (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHL (childHL (childHL (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHL (childHL (childHL (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHH (childHL (childHL (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHH (childHL (childHL (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 2 (childHH (childHL (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))
                (by
                  have h : ((childLL (childHH (childHL (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLL (childHH (childHL (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childLH (childHH (childHL (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLH (childHH (childHL (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHL (childHH (childHL (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHL (childHH (childHL (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHH (childHH (childHL (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHH (childHH (childHL (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)))
        (by
          exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))
            (by
              exact adaptiveCoverCheck_succ_of_children 2 (childLL (childHH (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))
                (by
                  have h : ((childLL (childLL (childHH (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLL (childLL (childHH (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childLH (childLL (childHH (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLH (childLL (childHH (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHL (childLL (childHH (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHL (childLL (childHH (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHH (childLL (childHH (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHH (childLL (childHH (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 2 (childLH (childHH (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))
                (by
                  have h : ((childLL (childLH (childHH (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLL (childLH (childHH (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childLH (childLH (childHH (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLH (childLH (childHH (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHL (childLH (childHH (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHL (childLH (childHH (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHH (childLH (childHH (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHH (childLH (childHH (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 2 (childHL (childHH (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))
                (by
                  have h : ((childLL (childHL (childHH (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLL (childHL (childHH (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childLH (childHL (childHH (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLH (childHL (childHH (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHL (childHL (childHH (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHL (childHL (childHH (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHH (childHL (childHH (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHH (childHL (childHH (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 2 (childHH (childHH (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))
                (by
                  have h : ((childLL (childHH (childHH (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLL (childHH (childHH (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childLH (childHH (childHH (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLH (childHH (childHH (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHL (childHH (childHH (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHL (childHH (childHH (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHH (childHH (childHH (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHH (childHH (childHH (childLL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h))))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))
        (by
          exact adaptiveCoverCheck_succ_of_children 3 (childLL (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))
            (by
              have h : ((childLL (childLL (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLL (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))) h)
            (by
              have h : ((childLH (childLL (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLL (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))) h)
            (by
              exact adaptiveCoverCheck_succ_of_children 2 (childHL (childLL (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))
                (by
                  have h : ((childLL (childHL (childLL (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLL (childHL (childLL (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childLH (childHL (childLL (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLH (childHL (childLL (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHL (childHL (childLL (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHL (childHL (childLL (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHH (childHL (childLL (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHH (childHL (childLL (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 2 (childHH (childLL (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))
                (by
                  have h : ((childLL (childHH (childLL (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLL (childHH (childLL (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childLH (childHH (childLL (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLH (childHH (childLL (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHL (childHH (childLL (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHL (childHH (childLL (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHH (childHH (childLL (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHH (childHH (childLL (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)))
        (by
          exact adaptiveCoverCheck_succ_of_children 3 (childLH (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))
            (by
              have h : ((childLL (childLH (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLH (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))) h)
            (by
              have h : ((childLH (childLH (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLH (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))) h)
            (by
              exact adaptiveCoverCheck_succ_of_children 2 (childHL (childLH (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))
                (by
                  have h : ((childLL (childHL (childLH (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLL (childHL (childLH (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childLH (childHL (childLH (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLH (childHL (childLH (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHL (childHL (childLH (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHL (childHL (childLH (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHH (childHL (childLH (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHH (childHL (childLH (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 2 (childHH (childLH (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))
                (by
                  have h : ((childLL (childHH (childLH (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLL (childHH (childLH (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childLH (childHH (childLH (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLH (childHH (childLH (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHL (childHH (childLH (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHL (childHH (childLH (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHH (childHH (childLH (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHH (childHH (childLH (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)))
        (by
          exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))
            (by
              exact adaptiveCoverCheck_succ_of_children 2 (childLL (childHL (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))
                (by
                  have h : ((childLL (childLL (childHL (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLL (childLL (childHL (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childLH (childLL (childHL (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLH (childLL (childHL (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHL (childLL (childHL (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHL (childLL (childHL (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHH (childLL (childHL (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHH (childLL (childHL (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 2 (childLH (childHL (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))
                (by
                  have h : ((childLL (childLH (childHL (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLL (childLH (childHL (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childLH (childLH (childHL (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLH (childLH (childHL (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHL (childLH (childHL (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHL (childLH (childHL (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHH (childLH (childHL (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHH (childLH (childHL (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 2 (childHL (childHL (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))
                (by
                  have h : ((childLL (childHL (childHL (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLL (childHL (childHL (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childLH (childHL (childHL (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLH (childHL (childHL (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHL (childHL (childHL (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHL (childHL (childHL (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHH (childHL (childHL (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHH (childHL (childHL (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 2 (childHH (childHL (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))
                (by
                  have h : ((childLL (childHH (childHL (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLL (childHH (childHL (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childLH (childHH (childHL (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLH (childHH (childHL (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHL (childHH (childHL (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHL (childHH (childHL (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHH (childHH (childHL (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHH (childHH (childHL (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)))
        (by
          exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))
            (by
              exact adaptiveCoverCheck_succ_of_children 2 (childLL (childHH (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))
                (by
                  have h : ((childLL (childLL (childHH (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLL (childLL (childHH (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childLH (childLL (childHH (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLH (childLL (childHH (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHL (childLL (childHH (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHL (childLL (childHH (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHH (childLL (childHH (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHH (childLL (childHH (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 2 (childLH (childHH (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))
                (by
                  have h : ((childLL (childLH (childHH (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLL (childLH (childHH (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childLH (childLH (childHH (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLH (childLH (childHH (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHL (childLH (childHH (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHL (childLH (childHH (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHH (childLH (childHH (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHH (childLH (childHH (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 2 (childHL (childHH (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))
                (by
                  have h : ((childLL (childHL (childHH (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLL (childHL (childHH (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childLH (childHL (childHH (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLH (childHL (childHH (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHL (childHL (childHH (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHL (childHL (childHH (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHH (childHL (childHH (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHH (childHL (childHH (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 2 (childHH (childHH (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))
                (by
                  have h : ((childLL (childHH (childHH (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLL (childHH (childHH (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childLH (childHH (childHH (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLH (childHH (childHH (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHL (childHH (childHH (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHL (childHH (childHH (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHH (childHH (childHH (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHH (childHH (childHH (childLH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h))))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))
        (by
          exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))
            (by
              have h : ((childLL (childLL (childHL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLL (childHL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))) h)
            (by
              have h : ((childLH (childLL (childHL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLL (childHL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))) h)
            (by
              have h : ((childHL (childLL (childHL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childLL (childHL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))) h)
            (by
              have h : ((childHH (childLL (childHL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childLL (childHL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))
            (by
              have h : ((childLL (childLH (childHL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLH (childHL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))) h)
            (by
              have h : ((childLH (childLH (childHL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLH (childHL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))) h)
            (by
              have h : ((childHL (childLH (childHL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childLH (childHL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))) h)
            (by
              have h : ((childHH (childLH (childHL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childLH (childHL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))) h))
        (by
          have h : ((childHL (childHL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))) h)
        (by
          have h : ((childHH (childHL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))
        (by
          exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))
            (by
              have h : ((childLL (childLL (childHH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLL (childHH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))) h)
            (by
              have h : ((childLH (childLL (childHH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLL (childHH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))) h)
            (by
              have h : ((childHL (childLL (childHH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childLL (childHH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))) h)
            (by
              have h : ((childHH (childLL (childHH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childLL (childHH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))
            (by
              have h : ((childLL (childLH (childHH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLH (childHH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))) h)
            (by
              have h : ((childLH (childLH (childHH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLH (childHH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))) h)
            (by
              have h : ((childHL (childLH (childHH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childLH (childHH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))) h)
            (by
              have h : ((childHH (childLH (childHH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childLH (childHH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))) h))
        (by
          have h : ((childHL (childHH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))) h)
        (by
          have h : ((childHH (childHH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHH (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))) h))

end PartE
end GerverSofa
