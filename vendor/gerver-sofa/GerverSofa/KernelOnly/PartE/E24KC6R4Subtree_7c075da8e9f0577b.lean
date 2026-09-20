import GerverSofa.KernelOnly.PartE.E24KC2ProofHelpers

/-! KC6R4 explicit terminal-certificate subtree. No adaptive search. -/
noncomputable section

namespace GerverSofa
namespace PartE

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111133113__c1__c1__c1__c1 :
    adaptiveCoverCheck 5 (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))
        (by
          have h : ((childLL (childLL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))) h)
        (by
          have h : ((childLH (childLL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))) h)
        (by
          have h : ((childHL (childLL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childLL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))) h)
        (by
          have h : ((childHH (childLL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childLL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))) h))
    (by
      have h : ((childLH (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))
        (by
          have h : ((childLL (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))) h)
        (by
          have h : ((childLH (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))) h)
        (by
          exact adaptiveCoverCheck_succ_of_children 2 (childHL (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))
            (by
              have h : ((childLL (childHL (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 (childLL (childHL (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)
            (by
              have h : ((childLH (childHL (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 (childLH (childHL (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)
            (by
              exact adaptiveCoverCheck_succ_of_children 1 (childHL (childHL (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))
                (by
                  have h : ((childLL (childHL (childHL (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHL (childHL (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
                (by
                  have h : ((childLH (childHL (childHL (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHL (childHL (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
                (by
                  exact adaptiveCoverCheck_succ_of_children 0 (childHL (childHL (childHL (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))
                    (by
                      have h : ((childLL (childHL (childHL (childHL (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childHL (childHL (childHL (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                    (by
                      have h : ((childLH (childHL (childHL (childHL (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childHL (childHL (childHL (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                    (by
                      have h : ((childHL (childHL (childHL (childHL (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childHL (childHL (childHL (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                    (by
                      have h : ((childHH (childHL (childHL (childHL (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childHL (childHL (childHL (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h))
                (by
                  exact adaptiveCoverCheck_succ_of_children 0 (childHH (childHL (childHL (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))
                    (by
                      have h : ((childLL (childHH (childHL (childHL (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childHH (childHL (childHL (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                    (by
                      have h : ((childLH (childHH (childHL (childHL (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childHH (childHL (childHL (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                    (by
                      have h : ((childHL (childHH (childHL (childHL (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childHH (childHL (childHL (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                    (by
                      have h : ((childHH (childHH (childHL (childHL (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childHH (childHL (childHL (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)))
            (by
              exact adaptiveCoverCheck_succ_of_children 1 (childHH (childHL (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))
                (by
                  have h : ((childLL (childHH (childHL (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHH (childHL (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
                (by
                  have h : ((childLH (childHH (childHL (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHH (childHL (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
                (by
                  exact adaptiveCoverCheck_succ_of_children 0 (childHL (childHH (childHL (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))
                    (by
                      have h : ((childLL (childHL (childHH (childHL (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childHL (childHH (childHL (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                    (by
                      have h : ((childLH (childHL (childHH (childHL (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childHL (childHH (childHL (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                    (by
                      have h : ((childHL (childHL (childHH (childHL (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childHL (childHH (childHL (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                    (by
                      have h : ((childHH (childHL (childHH (childHL (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childHL (childHH (childHL (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h))
                (by
                  exact adaptiveCoverCheck_succ_of_children 0 (childHH (childHH (childHL (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))
                    (by
                      have h : ((childLL (childHH (childHH (childHL (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childHH (childHH (childHL (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                    (by
                      have h : ((childLH (childHH (childHH (childHL (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childHH (childHH (childHL (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                    (by
                      have h : ((childHL (childHH (childHH (childHL (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childHH (childHH (childHL (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                    (by
                      have h : ((childHH (childHH (childHH (childHL (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childHH (childHH (childHL (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h))))
        (by
          exact adaptiveCoverCheck_succ_of_children 2 (childHH (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))
            (by
              have h : ((childLL (childHH (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 (childLL (childHH (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)
            (by
              have h : ((childLH (childHH (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 (childLH (childHH (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)
            (by
              exact adaptiveCoverCheck_succ_of_children 1 (childHL (childHH (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))
                (by
                  have h : ((childLL (childHL (childHH (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHL (childHH (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
                (by
                  have h : ((childLH (childHL (childHH (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHL (childHH (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
                (by
                  exact adaptiveCoverCheck_succ_of_children 0 (childHL (childHL (childHH (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))
                    (by
                      have h : ((childLL (childHL (childHL (childHH (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childHL (childHL (childHH (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                    (by
                      have h : ((childLH (childHL (childHL (childHH (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childHL (childHL (childHH (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                    (by
                      have h : ((childHL (childHL (childHL (childHH (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childHL (childHL (childHH (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                    (by
                      have h : ((childHH (childHL (childHL (childHH (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childHL (childHL (childHH (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h))
                (by
                  exact adaptiveCoverCheck_succ_of_children 0 (childHH (childHL (childHH (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))
                    (by
                      have h : ((childLL (childHH (childHL (childHH (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childHH (childHL (childHH (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                    (by
                      have h : ((childLH (childHH (childHL (childHH (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childHH (childHL (childHH (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                    (by
                      have h : ((childHL (childHH (childHL (childHH (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childHH (childHL (childHH (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                    (by
                      have h : ((childHH (childHH (childHL (childHH (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childHH (childHL (childHH (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)))
            (by
              exact adaptiveCoverCheck_succ_of_children 1 (childHH (childHH (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))
                (by
                  have h : ((childLL (childHH (childHH (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHH (childHH (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
                (by
                  have h : ((childLH (childHH (childHH (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHH (childHH (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
                (by
                  exact adaptiveCoverCheck_succ_of_children 0 (childHL (childHH (childHH (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))
                    (by
                      have h : ((childLL (childHL (childHH (childHH (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childHL (childHH (childHH (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                    (by
                      have h : ((childLH (childHL (childHH (childHH (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childHL (childHH (childHH (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                    (by
                      have h : ((childHL (childHL (childHH (childHH (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childHL (childHH (childHH (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                    (by
                      have h : ((childHH (childHL (childHH (childHH (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childHL (childHH (childHH (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h))
                (by
                  exact adaptiveCoverCheck_succ_of_children 0 (childHH (childHH (childHH (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))
                    (by
                      have h : ((childLL (childHH (childHH (childHH (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childHH (childHH (childHH (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                    (by
                      have h : ((childLH (childHH (childHH (childHH (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childHH (childHH (childHH (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                    (by
                      have h : ((childHL (childHH (childHH (childHH (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childHH (childHH (childHH (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                    (by
                      have h : ((childHH (childHH (childHH (childHH (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childHH (childHH (childHH (childHL (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)))))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))
        (by
          have h : ((childLL (childHH (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childHH (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))) h)
        (by
          have h : ((childLH (childHH (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childHH (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))) h)
        (by
          exact adaptiveCoverCheck_succ_of_children 2 (childHL (childHH (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))
            (by
              have h : ((childLL (childHL (childHH (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 (childLL (childHL (childHH (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)
            (by
              have h : ((childLH (childHL (childHH (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 (childLH (childHL (childHH (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)
            (by
              exact adaptiveCoverCheck_succ_of_children 1 (childHL (childHL (childHH (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))
                (by
                  have h : ((childLL (childHL (childHL (childHH (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHL (childHL (childHH (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
                (by
                  have h : ((childLH (childHL (childHL (childHH (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHL (childHL (childHH (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
                (by
                  exact adaptiveCoverCheck_succ_of_children 0 (childHL (childHL (childHL (childHH (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))
                    (by
                      have h : ((childLL (childHL (childHL (childHL (childHH (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childHL (childHL (childHL (childHH (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                    (by
                      have h : ((childLH (childHL (childHL (childHL (childHH (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childHL (childHL (childHL (childHH (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                    (by
                      have h : ((childHL (childHL (childHL (childHL (childHH (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childHL (childHL (childHL (childHH (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                    (by
                      have h : ((childHH (childHL (childHL (childHL (childHH (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childHL (childHL (childHL (childHH (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h))
                (by
                  exact adaptiveCoverCheck_succ_of_children 0 (childHH (childHL (childHL (childHH (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))
                    (by
                      have h : ((childLL (childHH (childHL (childHL (childHH (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childHH (childHL (childHL (childHH (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                    (by
                      have h : ((childLH (childHH (childHL (childHL (childHH (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childHH (childHL (childHL (childHH (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                    (by
                      have h : ((childHL (childHH (childHL (childHL (childHH (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childHH (childHL (childHL (childHH (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                    (by
                      have h : ((childHH (childHH (childHL (childHL (childHH (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childHH (childHL (childHL (childHH (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)))
            (by
              exact adaptiveCoverCheck_succ_of_children 1 (childHH (childHL (childHH (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))
                (by
                  have h : ((childLL (childHH (childHL (childHH (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHH (childHL (childHH (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
                (by
                  have h : ((childLH (childHH (childHL (childHH (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHH (childHL (childHH (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
                (by
                  exact adaptiveCoverCheck_succ_of_children 0 (childHL (childHH (childHL (childHH (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))
                    (by
                      have h : ((childLL (childHL (childHH (childHL (childHH (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childHL (childHH (childHL (childHH (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                    (by
                      have h : ((childLH (childHL (childHH (childHL (childHH (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childHL (childHH (childHL (childHH (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                    (by
                      have h : ((childHL (childHL (childHH (childHL (childHH (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childHL (childHH (childHL (childHH (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                    (by
                      have h : ((childHH (childHL (childHH (childHL (childHH (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childHL (childHH (childHL (childHH (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h))
                (by
                  exact adaptiveCoverCheck_succ_of_children 0 (childHH (childHH (childHL (childHH (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))
                    (by
                      have h : ((childLL (childHH (childHH (childHL (childHH (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childHH (childHH (childHL (childHH (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                    (by
                      have h : ((childLH (childHH (childHH (childHL (childHH (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childHH (childHH (childHL (childHH (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                    (by
                      have h : ((childHL (childHH (childHH (childHL (childHH (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childHH (childHH (childHL (childHH (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h)
                    (by
                      have h : ((childHH (childHH (childHH (childHL (childHH (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childHH (childHH (childHL (childHH (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))) h))))
        (by
          exact adaptiveCoverCheck_succ_of_children 2 (childHH (childHH (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))
            (by
              have h : ((childLL (childHH (childHH (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 (childLL (childHH (childHH (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)
            (by
              have h : ((childLH (childHH (childHH (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 (childLH (childHH (childHH (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))) h)
            (by
              exact adaptiveCoverCheck_succ_of_children 1 (childHL (childHH (childHH (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))
                (by
                  have h : ((childLL (childHL (childHH (childHH (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHL (childHH (childHH (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
                (by
                  have h : ((childLH (childHL (childHH (childHH (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHL (childHH (childHH (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
                (by
                  have h : ((childHL (childHL (childHH (childHH (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHL (childHH (childHH (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
                (by
                  have h : ((childHH (childHL (childHH (childHH (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHL (childHH (childHH (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 1 (childHH (childHH (childHH (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))
                (by
                  have h : ((childLL (childHH (childHH (childHH (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHH (childHH (childHH (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
                (by
                  have h : ((childLH (childHH (childHH (childHH (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHH (childHH (childHH (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
                (by
                  have h : ((childHL (childHH (childHH (childHH (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHH (childHH (childHH (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h)
                (by
                  have h : ((childHH (childHH (childHH (childHH (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHH (childHH (childHH (childLH (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))))) h))))

end PartE
end GerverSofa
