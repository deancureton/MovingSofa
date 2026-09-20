import GerverSofa.KernelOnly.PartE.E24KC2ProofHelpers

/-! KC6R4 explicit terminal-certificate subtree. No adaptive search. -/
noncomputable section

namespace GerverSofa
namespace PartE

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0000220021__c1__c0__c2 :
    adaptiveCoverCheck 6 (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))
        (by
          exact adaptiveCoverCheck_succ_of_children 3 (childLL (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))
            (by
              have h : ((childLL (childLL (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLL (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))) h)
            (by
              have h : ((childLH (childLL (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLL (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))) h)
            (by
              exact adaptiveCoverCheck_succ_of_children 2 (childHL (childLL (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))
                (by
                  have h : ((childLL (childHL (childLL (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLL (childHL (childLL (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childLH (childHL (childLL (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLH (childHL (childLL (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHL (childHL (childLL (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHL (childHL (childLL (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHH (childHL (childLL (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHH (childHL (childLL (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 2 (childHH (childLL (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))
                (by
                  have h : ((childLL (childHH (childLL (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLL (childHH (childLL (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childLH (childHH (childLL (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLH (childHH (childLL (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHL (childHH (childLL (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHL (childHH (childLL (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHH (childHH (childLL (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHH (childHH (childLL (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)))
        (by
          exact adaptiveCoverCheck_succ_of_children 3 (childLH (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))
            (by
              have h : ((childLL (childLH (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLH (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))) h)
            (by
              have h : ((childLH (childLH (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLH (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))) h)
            (by
              exact adaptiveCoverCheck_succ_of_children 2 (childHL (childLH (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))
                (by
                  have h : ((childLL (childHL (childLH (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLL (childHL (childLH (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childLH (childHL (childLH (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLH (childHL (childLH (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHL (childHL (childLH (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHL (childHL (childLH (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHH (childHL (childLH (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHH (childHL (childLH (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 2 (childHH (childLH (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))
                (by
                  have h : ((childLL (childHH (childLH (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLL (childHH (childLH (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childLH (childHH (childLH (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLH (childHH (childLH (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHL (childHH (childLH (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHL (childHH (childLH (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHH (childHH (childLH (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHH (childHH (childLH (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)))
        (by
          exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))
            (by
              exact adaptiveCoverCheck_succ_of_children 2 (childLL (childHL (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))
                (by
                  have h : ((childLL (childLL (childHL (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLL (childLL (childHL (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childLH (childLL (childHL (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLH (childLL (childHL (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHL (childLL (childHL (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHL (childLL (childHL (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHH (childLL (childHL (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHH (childLL (childHL (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 2 (childLH (childHL (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))
                (by
                  have h : ((childLL (childLH (childHL (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLL (childLH (childHL (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childLH (childLH (childHL (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLH (childLH (childHL (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHL (childLH (childHL (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHL (childLH (childHL (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHH (childLH (childHL (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHH (childLH (childHL (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 2 (childHL (childHL (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))
                (by
                  have h : ((childLL (childHL (childHL (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLL (childHL (childHL (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childLH (childHL (childHL (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLH (childHL (childHL (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHL (childHL (childHL (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHL (childHL (childHL (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHH (childHL (childHL (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHH (childHL (childHL (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 2 (childHH (childHL (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))
                (by
                  have h : ((childLL (childHH (childHL (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLL (childHH (childHL (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childLH (childHH (childHL (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLH (childHH (childHL (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHL (childHH (childHL (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHL (childHH (childHL (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHH (childHH (childHL (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHH (childHH (childHL (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)))
        (by
          exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))
            (by
              exact adaptiveCoverCheck_succ_of_children 2 (childLL (childHH (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))
                (by
                  have h : ((childLL (childLL (childHH (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLL (childLL (childHH (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childLH (childLL (childHH (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLH (childLL (childHH (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHL (childLL (childHH (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHL (childLL (childHH (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHH (childLL (childHH (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHH (childLL (childHH (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 2 (childLH (childHH (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))
                (by
                  have h : ((childLL (childLH (childHH (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLL (childLH (childHH (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childLH (childLH (childHH (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLH (childLH (childHH (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHL (childLH (childHH (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHL (childLH (childHH (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHH (childLH (childHH (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHH (childLH (childHH (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 2 (childHL (childHH (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))
                (by
                  have h : ((childLL (childHL (childHH (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLL (childHL (childHH (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childLH (childHL (childHH (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLH (childHL (childHH (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHL (childHL (childHH (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHL (childHL (childHH (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHH (childHL (childHH (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHH (childHL (childHH (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 2 (childHH (childHH (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))
                (by
                  have h : ((childLL (childHH (childHH (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLL (childHH (childHH (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childLH (childHH (childHH (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLH (childHH (childHH (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHL (childHH (childHH (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHL (childHH (childHH (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHH (childHH (childHH (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHH (childHH (childHH (childLL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h))))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))
        (by
          exact adaptiveCoverCheck_succ_of_children 3 (childLL (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))
            (by
              have h : ((childLL (childLL (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLL (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))) h)
            (by
              have h : ((childLH (childLL (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLL (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))) h)
            (by
              exact adaptiveCoverCheck_succ_of_children 2 (childHL (childLL (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))
                (by
                  have h : ((childLL (childHL (childLL (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLL (childHL (childLL (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childLH (childHL (childLL (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLH (childHL (childLL (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHL (childHL (childLL (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHL (childHL (childLL (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHH (childHL (childLL (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHH (childHL (childLL (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 2 (childHH (childLL (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))
                (by
                  have h : ((childLL (childHH (childLL (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLL (childHH (childLL (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childLH (childHH (childLL (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLH (childHH (childLL (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHL (childHH (childLL (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHL (childHH (childLL (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHH (childHH (childLL (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHH (childHH (childLL (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)))
        (by
          exact adaptiveCoverCheck_succ_of_children 3 (childLH (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))
            (by
              have h : ((childLL (childLH (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLH (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))) h)
            (by
              have h : ((childLH (childLH (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLH (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))) h)
            (by
              exact adaptiveCoverCheck_succ_of_children 2 (childHL (childLH (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))
                (by
                  have h : ((childLL (childHL (childLH (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLL (childHL (childLH (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childLH (childHL (childLH (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLH (childHL (childLH (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHL (childHL (childLH (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHL (childHL (childLH (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHH (childHL (childLH (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHH (childHL (childLH (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 2 (childHH (childLH (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))
                (by
                  have h : ((childLL (childHH (childLH (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLL (childHH (childLH (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childLH (childHH (childLH (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLH (childHH (childLH (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHL (childHH (childLH (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHL (childHH (childLH (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHH (childHH (childLH (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHH (childHH (childLH (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)))
        (by
          exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))
            (by
              exact adaptiveCoverCheck_succ_of_children 2 (childLL (childHL (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))
                (by
                  have h : ((childLL (childLL (childHL (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLL (childLL (childHL (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childLH (childLL (childHL (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLH (childLL (childHL (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHL (childLL (childHL (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHL (childLL (childHL (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHH (childLL (childHL (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHH (childLL (childHL (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 2 (childLH (childHL (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))
                (by
                  have h : ((childLL (childLH (childHL (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLL (childLH (childHL (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childLH (childLH (childHL (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLH (childLH (childHL (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHL (childLH (childHL (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHL (childLH (childHL (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHH (childLH (childHL (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHH (childLH (childHL (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 2 (childHL (childHL (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))
                (by
                  have h : ((childLL (childHL (childHL (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLL (childHL (childHL (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childLH (childHL (childHL (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLH (childHL (childHL (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHL (childHL (childHL (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHL (childHL (childHL (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHH (childHL (childHL (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHH (childHL (childHL (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 2 (childHH (childHL (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))
                (by
                  have h : ((childLL (childHH (childHL (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLL (childHH (childHL (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childLH (childHH (childHL (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLH (childHH (childHL (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHL (childHH (childHL (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHL (childHH (childHL (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHH (childHH (childHL (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHH (childHH (childHL (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)))
        (by
          exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))
            (by
              exact adaptiveCoverCheck_succ_of_children 2 (childLL (childHH (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))
                (by
                  have h : ((childLL (childLL (childHH (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLL (childLL (childHH (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childLH (childLL (childHH (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLH (childLL (childHH (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHL (childLL (childHH (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHL (childLL (childHH (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHH (childLL (childHH (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHH (childLL (childHH (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 2 (childLH (childHH (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))
                (by
                  have h : ((childLL (childLH (childHH (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLL (childLH (childHH (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childLH (childLH (childHH (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLH (childLH (childHH (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHL (childLH (childHH (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHL (childLH (childHH (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHH (childLH (childHH (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHH (childLH (childHH (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 2 (childHL (childHH (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))
                (by
                  have h : ((childLL (childHL (childHH (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLL (childHL (childHH (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childLH (childHL (childHH (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLH (childHL (childHH (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHL (childHL (childHH (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHL (childHL (childHH (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHH (childHL (childHH (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHH (childHL (childHH (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 2 (childHH (childHH (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))
                (by
                  have h : ((childLL (childHH (childHH (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLL (childHH (childHH (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childLH (childHH (childHH (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childLH (childHH (childHH (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHL (childHH (childHH (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHL (childHH (childHH (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h)
                (by
                  have h : ((childHH (childHH (childHH (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 2 (childHH (childHH (childHH (childLH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))) h))))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))
        (by
          exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))
            (by
              have h : ((childLL (childLL (childHL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLL (childHL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))) h)
            (by
              have h : ((childLH (childLL (childHL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLL (childHL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))) h)
            (by
              have h : ((childHL (childLL (childHL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childLL (childHL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))) h)
            (by
              have h : ((childHH (childLL (childHL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childLL (childHL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))
            (by
              have h : ((childLL (childLH (childHL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLH (childHL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))) h)
            (by
              have h : ((childLH (childLH (childHL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLH (childHL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))) h)
            (by
              have h : ((childHL (childLH (childHL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childLH (childHL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))) h)
            (by
              have h : ((childHH (childLH (childHL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childLH (childHL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))) h))
        (by
          have h : ((childHL (childHL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))) h)
        (by
          have h : ((childHH (childHL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))
        (by
          exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))
            (by
              have h : ((childLL (childLL (childHH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLL (childHH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))) h)
            (by
              have h : ((childLH (childLL (childHH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLL (childHH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))) h)
            (by
              have h : ((childHL (childLL (childHH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childLL (childHH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))) h)
            (by
              have h : ((childHH (childLL (childHH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childLL (childHH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))
            (by
              have h : ((childLL (childLH (childHH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLH (childHH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))) h)
            (by
              have h : ((childLH (childLH (childHH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLH (childHH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))) h)
            (by
              have h : ((childHL (childLH (childHH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childLH (childHH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))) h)
            (by
              have h : ((childHH (childLH (childHH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childLH (childHH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))) h))
        (by
          have h : ((childHL (childHH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))) h)
        (by
          have h : ((childHH (childHH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHL (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))))) h))

end PartE
end GerverSofa
