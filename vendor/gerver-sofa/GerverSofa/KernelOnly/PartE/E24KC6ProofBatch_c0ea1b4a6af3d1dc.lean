import GerverSofa.KernelOnly.PartE.E24KC2ProofHelpers

/-! E24KC6 explicit proof-producing certificate batch. -/
noncomputable section

namespace GerverSofa
namespace PartE

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111132101 :
    adaptiveCoverCheck 9 (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childLL (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childLL (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHL (childLL (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childHL (childLL (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHL (childLL (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childHL (childLL (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHL (childLL (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childHL (childLL (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHL (childLL (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childHL (childLL (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHL (childLL (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHH (childLL (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childHH (childLL (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHH (childLL (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childHH (childLL (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHH (childLL (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childHH (childLL (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHH (childLL (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childHH (childLL (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHH (childLL (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childLH (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childLH (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHL (childLH (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childHL (childLH (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHL (childLH (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childHL (childLH (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHL (childLH (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childHL (childLH (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHL (childLH (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childHL (childLH (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHL (childLH (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHH (childLH (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childHH (childLH (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHH (childLH (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childHH (childLH (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHH (childLH (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childHH (childLH (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHH (childLH (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childHH (childLH (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHH (childLH (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLL (childHL (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childLL (childHL (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childLL (childHL (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childLL (childHL (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childLL (childHL (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childLL (childHL (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childLL (childHL (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childLL (childHL (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childLL (childHL (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLH (childHL (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childLH (childHL (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childLH (childHL (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childLH (childHL (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childLH (childHL (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childLH (childHL (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childLH (childHL (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childLH (childHL (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childLH (childHL (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHL (childHL (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childHL (childHL (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHL (childHL (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childHL (childHL (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHL (childHL (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childHL (childHL (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHL (childHL (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childHL (childHL (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHL (childHL (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHH (childHL (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childHH (childHL (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHH (childHL (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childHH (childHL (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHH (childHL (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childHH (childHL (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHH (childHL (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childHH (childHL (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHH (childHL (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLL (childHH (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childLL (childHH (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childLL (childHH (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childLL (childHH (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childLL (childHH (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childLL (childHH (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childLL (childHH (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childLL (childHH (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childLL (childHH (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLH (childHH (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childLH (childHH (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childLH (childHH (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childLH (childHH (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childLH (childHH (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childLH (childHH (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childLH (childHH (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childLH (childHH (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childLH (childHH (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHL (childHH (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childHL (childHH (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHL (childHH (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childHL (childHH (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHL (childHH (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childHL (childHH (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHL (childHH (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childHL (childHH (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHL (childHH (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHH (childHH (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childHH (childHH (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHH (childHH (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childHH (childHH (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHH (childHH (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childHH (childHH (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHH (childHH (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childHH (childHH (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHH (childHH (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111132102 :
    adaptiveCoverCheck 9 (childHL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childLL (childHL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childHL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childLL (childHL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childHL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childLL (childHL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childLL (childHL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childLH (childHL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childHL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childLH (childHL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childHL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childLH (childHL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childLH (childHL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))
    (by
      have h : ((childHL (childHL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childHL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111132103 :
    adaptiveCoverCheck 9 (childHH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childLL (childHH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childHH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childLL (childHH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childHH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childLL (childHH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childLL (childHH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childLH (childHH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childHH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childLH (childHH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childHH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childLH (childHH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childLH (childHH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))
    (by
      have h : ((childHL (childHH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childHH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111132110 :
    adaptiveCoverCheck 9 (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childLL (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childLL (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHL (childLL (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childHL (childLL (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHL (childLL (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childHL (childLL (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHL (childLL (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childHL (childLL (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHL (childLL (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childHL (childLL (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHL (childLL (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHH (childLL (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childHH (childLL (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHH (childLL (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childHH (childLL (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHH (childLL (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childHH (childLL (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHH (childLL (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childHH (childLL (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHH (childLL (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childLH (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childLH (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHL (childLH (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childHL (childLH (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHL (childLH (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childHL (childLH (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHL (childLH (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childHL (childLH (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHL (childLH (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childHL (childLH (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHL (childLH (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHH (childLH (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childHH (childLH (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHH (childLH (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childHH (childLH (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHH (childLH (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childHH (childLH (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHH (childLH (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childHH (childLH (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHH (childLH (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLL (childHL (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childLL (childHL (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childLL (childHL (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childLL (childHL (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childLL (childHL (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childLL (childHL (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childLL (childHL (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childLL (childHL (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childLL (childHL (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLH (childHL (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childLH (childHL (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childLH (childHL (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childLH (childHL (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childLH (childHL (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childLH (childHL (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childLH (childHL (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childLH (childHL (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childLH (childHL (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHL (childHL (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childHL (childHL (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHL (childHL (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childHL (childHL (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHL (childHL (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childHL (childHL (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHL (childHL (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childHL (childHL (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHL (childHL (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHH (childHL (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childHH (childHL (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHH (childHL (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childHH (childHL (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHH (childHL (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childHH (childHL (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHH (childHL (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childHH (childHL (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHH (childHL (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLL (childHH (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childLL (childHH (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childLL (childHH (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childLL (childHH (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childLL (childHH (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childLL (childHH (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childLL (childHH (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childLL (childHH (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childLL (childHH (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLH (childHH (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childLH (childHH (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childLH (childHH (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childLH (childHH (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childLH (childHH (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childLH (childHH (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childLH (childHH (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childLH (childHH (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childLH (childHH (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHL (childHH (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childHL (childHH (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHL (childHH (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childHL (childHH (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHL (childHH (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childHL (childHH (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHL (childHH (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childHL (childHH (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHL (childHH (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHH (childHH (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childHH (childHH (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHH (childHH (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childHH (childHH (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHH (childHH (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childHH (childHH (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHH (childHH (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childHH (childHH (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHH (childHH (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111132111 :
    adaptiveCoverCheck 9 (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childLL (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childLL (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHL (childLL (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childHL (childLL (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHL (childLL (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childHL (childLL (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHL (childLL (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childHL (childLL (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHL (childLL (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childHL (childLL (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHL (childLL (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHH (childLL (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childHH (childLL (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHH (childLL (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childHH (childLL (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHH (childLL (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childHH (childLL (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHH (childLL (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childHH (childLL (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHH (childLL (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childLH (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childLH (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHL (childLH (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childHL (childLH (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHL (childLH (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childHL (childLH (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHL (childLH (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childHL (childLH (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHL (childLH (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childHL (childLH (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHL (childLH (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHH (childLH (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childHH (childLH (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHH (childLH (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childHH (childLH (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHH (childLH (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childHH (childLH (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHH (childLH (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childHH (childLH (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHH (childLH (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLL (childHL (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childLL (childHL (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childLL (childHL (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childLL (childHL (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childLL (childHL (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childLL (childHL (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childLL (childHL (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childLL (childHL (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childLL (childHL (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLH (childHL (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childLH (childHL (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childLH (childHL (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childLH (childHL (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childLH (childHL (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childLH (childHL (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childLH (childHL (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childLH (childHL (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childLH (childHL (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHL (childHL (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childHL (childHL (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHL (childHL (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childHL (childHL (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHL (childHL (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childHL (childHL (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHL (childHL (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childHL (childHL (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHL (childHL (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHH (childHL (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childHH (childHL (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHH (childHL (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childHH (childHL (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHH (childHL (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childHH (childHL (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHH (childHL (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childHH (childHL (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHH (childHL (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLL (childHH (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childLL (childHH (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childLL (childHH (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childLL (childHH (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childLL (childHH (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childLL (childHH (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childLL (childHH (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childLL (childHH (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childLL (childHH (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLH (childHH (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childLH (childHH (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childLH (childHH (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childLH (childHH (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childLH (childHH (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childLH (childHH (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childLH (childHH (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childLH (childHH (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childLH (childHH (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHL (childHH (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childHL (childHH (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHL (childHH (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childHL (childHH (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHL (childHH (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childHL (childHH (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHL (childHH (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childHL (childHH (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHL (childHH (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHH (childHH (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childHH (childHH (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHH (childHH (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childHH (childHH (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHH (childHH (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childHH (childHH (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHH (childHH (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childHH (childHH (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHH (childHH (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111132112 :
    adaptiveCoverCheck 9 (childHL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childLL (childHL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childHL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childLL (childHL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childHL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childLL (childHL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childLL (childHL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childLH (childHL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childHL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childLH (childHL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childHL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childLH (childHL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childLH (childHL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))
    (by
      have h : ((childHL (childHL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childHL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111132113 :
    adaptiveCoverCheck 9 (childHH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childLL (childHH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childHH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childLL (childHH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childHH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childLL (childHH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childLL (childHH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childLH (childHH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childHH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childLH (childHH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childHH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childLH (childHH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childLH (childHH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))
    (by
      have h : ((childHL (childHH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childHH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111133000 :
    adaptiveCoverCheck 9 (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childLL (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childLL (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHL (childLL (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childHL (childLL (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHL (childLL (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childHL (childLL (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHL (childLL (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childHL (childLL (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHL (childLL (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childHL (childLL (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHL (childLL (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHH (childLL (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childHH (childLL (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHH (childLL (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childHH (childLL (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHH (childLL (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childHH (childLL (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHH (childLL (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childHH (childLL (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHH (childLL (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childLH (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childLH (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHL (childLH (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childHL (childLH (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHL (childLH (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childHL (childLH (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHL (childLH (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childHL (childLH (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHL (childLH (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childHL (childLH (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHL (childLH (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHH (childLH (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childHH (childLH (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHH (childLH (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childHH (childLH (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHH (childLH (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childHH (childLH (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHH (childLH (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childHH (childLH (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHH (childLH (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLL (childHL (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childLL (childHL (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childLL (childHL (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childLL (childHL (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childLL (childHL (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childLL (childHL (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childLL (childHL (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childLL (childHL (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childLL (childHL (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLH (childHL (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childLH (childHL (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childLH (childHL (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childLH (childHL (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childLH (childHL (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childLH (childHL (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childLH (childHL (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childLH (childHL (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childLH (childHL (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHL (childHL (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childHL (childHL (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHL (childHL (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childHL (childHL (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHL (childHL (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childHL (childHL (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHL (childHL (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childHL (childHL (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHL (childHL (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHH (childHL (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childHH (childHL (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHH (childHL (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childHH (childHL (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHH (childHL (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childHH (childHL (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHH (childHL (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childHH (childHL (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHH (childHL (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLL (childHH (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childLL (childHH (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childLL (childHH (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childLL (childHH (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childLL (childHH (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childLL (childHH (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childLL (childHH (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childLL (childHH (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childLL (childHH (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLH (childHH (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childLH (childHH (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childLH (childHH (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childLH (childHH (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childLH (childHH (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childLH (childHH (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childLH (childHH (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childLH (childHH (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childLH (childHH (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHL (childHH (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childHL (childHH (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHL (childHH (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childHL (childHH (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHL (childHH (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childHL (childHH (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHL (childHH (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childHL (childHH (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHL (childHH (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHH (childHH (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childHH (childHH (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHH (childHH (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childHH (childHH (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHH (childHH (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childHH (childHH (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHH (childHH (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childHH (childHH (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHH (childHH (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111133001 :
    adaptiveCoverCheck 9 (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childLL (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childLL (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHL (childLL (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childHL (childLL (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHL (childLL (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childHL (childLL (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHL (childLL (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childHL (childLL (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHL (childLL (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childHL (childLL (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHL (childLL (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHH (childLL (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childHH (childLL (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHH (childLL (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childHH (childLL (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHH (childLL (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childHH (childLL (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHH (childLL (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childHH (childLL (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHH (childLL (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childLH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childLH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHL (childLH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childHL (childLH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHL (childLH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childHL (childLH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHL (childLH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childHL (childLH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHL (childLH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childHL (childLH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHL (childLH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h))
        (by
          have h : ((childHH (childLH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLL (childHL (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childLL (childHL (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childLL (childHL (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childLL (childHL (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childLL (childHL (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childLL (childHL (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childLL (childHL (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childLL (childHL (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childLL (childHL (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLH (childHL (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childLH (childHL (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childLH (childHL (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childLH (childHL (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childLH (childHL (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childLH (childHL (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childLH (childHL (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childLH (childHL (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childLH (childHL (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHL (childHL (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childHL (childHL (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHL (childHL (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childHL (childHL (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHL (childHL (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childHL (childHL (childHL (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childHL (childHL (childHL (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL (childHL (childHL (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childHL (childHL (childHL (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL (childHL (childHL (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHL (childHL (childHL (childHL (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL (childHL (childHL (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childHL (childHL (childHL (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL (childHL (childHL (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childHH (childHL (childHL (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childHH (childHL (childHL (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH (childHL (childHL (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childHH (childHL (childHL (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH (childHL (childHL (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHL (childHH (childHL (childHL (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH (childHL (childHL (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childHH (childHL (childHL (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH (childHL (childHL (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHH (childHL (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childHH (childHL (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHH (childHL (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childLH (childHH (childHL (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childLH (childHH (childHL (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childLH (childHH (childHL (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHL (childLH (childHH (childHL (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH (childHH (childHL (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childLH (childHH (childHL (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH (childHH (childHL (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childHL (childHH (childHL (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childHL (childHH (childHL (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL (childHH (childHL (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childHL (childHH (childHL (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL (childHH (childHL (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHL (childHL (childHH (childHL (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL (childHH (childHL (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childHL (childHH (childHL (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL (childHH (childHL (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childHH (childHH (childHL (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childHH (childHH (childHL (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH (childHH (childHL (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childHH (childHH (childHL (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH (childHH (childHL (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHL (childHH (childHH (childHL (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH (childHH (childHL (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childHH (childHH (childHL (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH (childHH (childHL (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLL (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childLL (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childLL (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childLL (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childLL (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childLL (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childLL (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childHH (childLL (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childHH (childLL (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH (childLL (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childHH (childLL (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH (childLL (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHL (childHH (childLL (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH (childLL (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childHH (childLL (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH (childLL (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLH (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childLH (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childLH (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childLH (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childLH (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childHL (childLH (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childHL (childLH (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL (childLH (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childHL (childLH (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL (childLH (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHL (childHL (childLH (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL (childLH (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childHL (childLH (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL (childLH (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childHH (childLH (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childHH (childLH (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH (childLH (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childHH (childLH (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH (childLH (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHL (childHH (childLH (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH (childLH (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childHH (childLH (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH (childLH (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHL (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childLL (childHL (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childLL (childHL (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childLL (childHL (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHL (childLL (childHL (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL (childHL (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childLL (childHL (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL (childHL (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childLH (childHL (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childLH (childHL (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childLH (childHL (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHL (childLH (childHL (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH (childHL (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childLH (childHL (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH (childHL (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childHL (childHL (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childHL (childHL (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL (childHL (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childHL (childHL (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL (childHL (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHL (childHL (childHL (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL (childHL (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childHL (childHL (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL (childHL (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childHH (childHL (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childHH (childHL (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH (childHL (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childHH (childHL (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH (childHL (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHL (childHH (childHL (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH (childHL (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childHH (childHL (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH (childHL (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHH (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childLL (childHH (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childLL (childHH (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childLL (childHH (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHL (childLL (childHH (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL (childHH (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childLL (childHH (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL (childHH (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childLH (childHH (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childLH (childHH (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childLH (childHH (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHL (childLH (childHH (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH (childHH (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childLH (childHH (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH (childHH (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childHL (childHH (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childHL (childHH (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL (childHH (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childHL (childHH (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL (childHH (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHL (childHL (childHH (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL (childHH (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childHL (childHH (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL (childHH (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childHH (childHH (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childHH (childHH (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH (childHH (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childHH (childHH (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH (childHH (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHL (childHH (childHH (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH (childHH (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childHH (childHH (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH (childHH (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111133002 :
    adaptiveCoverCheck 9 (childHL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childLL (childHL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childHL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childLL (childHL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childHL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childLL (childHL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childLL (childHL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLL (childLH (childHL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childLL (childLH (childHL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childLL (childLH (childHL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childLL (childLH (childHL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childLL (childLH (childHL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childLL (childLH (childHL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childLL (childLH (childHL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childLL (childLH (childHL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childLL (childLH (childHL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLH (childLH (childHL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childLH (childLH (childHL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childLH (childLH (childHL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childLH (childLH (childHL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childLH (childLH (childHL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childLH (childLH (childHL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childLH (childLH (childHL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childLH (childLH (childHL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childLH (childLH (childHL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h))
        (by
          have h : ((childHL (childLH (childHL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childLH (childHL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))
    (by
      have h : ((childHL (childHL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childHL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111133003 :
    adaptiveCoverCheck 9 (childHH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLL (childLL (childHH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childLL (childLL (childHH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childLL (childLL (childHH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childLL (childLL (childHH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childLL (childLL (childHH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childLL (childLL (childHH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childLL (childLL (childHH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childLL (childLL (childHH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childLL (childLL (childHH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLH (childLL (childHH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childLH (childLL (childHH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childLH (childLL (childHH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childLH (childLL (childHH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childLH (childLL (childHH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childLH (childLL (childHH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childLH (childLL (childHH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childLH (childLL (childHH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childLH (childLL (childHH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h))
        (by
          have h : ((childHL (childLL (childHH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childLL (childHH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLL (childLH (childHH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childLL (childLH (childHH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childLL (childLH (childHH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childLL (childLH (childHH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childLL (childLH (childHH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childLL (childLH (childHH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childLL (childLH (childHH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childLL (childLH (childHH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childLL (childLH (childHH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLH (childLH (childHH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childLH (childLH (childHH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childLH (childLH (childHH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childLH (childLH (childHH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childLH (childLH (childHH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childLH (childLH (childHH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childLH (childLH (childHH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childLH (childLH (childHH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childLH (childLH (childHH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h))
        (by
          have h : ((childHL (childLH (childHH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childLH (childHH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))
    (by
      have h : ((childHL (childHH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childHH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111133010 :
    adaptiveCoverCheck 9 (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childLL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childLL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childLL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childLL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childLH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childLH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childLH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childLH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLL (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childLL (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childLL (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childLL (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childLL (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childHL (childLL (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childHL (childLL (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL (childLL (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childHL (childLL (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL (childLL (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHL (childHL (childLL (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL (childLL (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childHL (childLL (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL (childLL (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childHH (childLL (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childHH (childLL (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH (childLL (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childHH (childLL (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH (childLL (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHL (childHH (childLL (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH (childLL (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childHH (childLL (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH (childLL (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLH (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childLH (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childLH (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childLH (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childLH (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childHL (childLH (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childHL (childLH (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL (childLH (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childHL (childLH (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL (childLH (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHL (childHL (childLH (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL (childLH (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childHL (childLH (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL (childLH (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childHH (childLH (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childHH (childLH (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH (childLH (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childHH (childLH (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH (childLH (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHL (childHH (childLH (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH (childLH (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childHH (childLH (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH (childLH (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHL (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childLL (childHL (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childLL (childHL (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childLL (childHL (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHL (childLL (childHL (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL (childHL (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childLL (childHL (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL (childHL (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childLH (childHL (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childLH (childHL (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childLH (childHL (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH (childHL (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHL (childLH (childHL (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH (childHL (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childLH (childHL (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH (childHL (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childHL (childHL (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childHL (childHL (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL (childHL (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childHL (childHL (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL (childHL (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHL (childHL (childHL (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL (childHL (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childHL (childHL (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL (childHL (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childHH (childHL (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childHH (childHL (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH (childHL (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childHH (childHL (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH (childHL (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHL (childHH (childHL (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH (childHL (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childHH (childHL (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH (childHL (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHH (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childLL (childHH (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childLL (childHH (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL (childHH (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childLL (childHH (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL (childHH (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHL (childLL (childHH (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL (childHH (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childLL (childHH (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL (childHH (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childLH (childHH (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childLH (childHH (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH (childHH (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childLH (childHH (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH (childHH (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHL (childLH (childHH (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH (childHH (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childLH (childHH (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH (childHH (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childHL (childHH (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childHL (childHH (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL (childHH (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childHL (childHH (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL (childHH (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHL (childHL (childHH (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL (childHH (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childHL (childHH (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL (childHH (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childHH (childHH (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childHH (childHH (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH (childHH (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childHH (childHH (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH (childHH (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHL (childHH (childHH (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH (childHH (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childHH (childHH (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH (childHH (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLL (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childLL (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childLL (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childLL (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childLL (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childHL (childLL (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childHL (childLL (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL (childLL (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childHL (childLL (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL (childLL (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHL (childHL (childLL (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL (childLL (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childHL (childLL (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL (childLL (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childHH (childLL (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childHH (childLL (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH (childLL (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childHH (childLL (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH (childLL (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHL (childHH (childLL (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH (childLL (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childHH (childLL (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH (childLL (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLH (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childLH (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childLH (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childLH (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childLH (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childHL (childLH (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childHL (childLH (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL (childLH (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childHL (childLH (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL (childLH (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHL (childHL (childLH (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL (childLH (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childHL (childLH (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL (childLH (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childHH (childLH (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childHH (childLH (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH (childLH (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childHH (childLH (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH (childLH (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHL (childHH (childLH (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH (childLH (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childHH (childLH (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH (childLH (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHL (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childLL (childHL (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childLL (childHL (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL (childHL (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childLL (childHL (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL (childHL (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHL (childLL (childHL (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL (childHL (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childLL (childHL (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL (childHL (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childLH (childHL (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childLH (childHL (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH (childHL (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childLH (childHL (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH (childHL (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHL (childLH (childHL (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH (childHL (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childLH (childHL (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH (childHL (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childHL (childHL (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childHL (childHL (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL (childHL (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childHL (childHL (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL (childHL (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHL (childHL (childHL (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL (childHL (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childHL (childHL (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL (childHL (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childHH (childHL (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childHH (childHL (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH (childHL (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childHH (childHL (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH (childHL (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHL (childHH (childHL (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH (childHL (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childHH (childHL (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH (childHL (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHH (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childLL (childHH (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childLL (childHH (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL (childHH (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childLL (childHH (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL (childHH (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHL (childLL (childHH (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL (childHH (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childLL (childHH (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL (childHH (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childLH (childHH (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childLH (childHH (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH (childHH (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childLH (childHH (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH (childHH (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHL (childLH (childHH (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH (childHH (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childLH (childHH (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH (childHH (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childHL (childHH (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childHL (childHH (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL (childHH (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childHL (childHH (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL (childHH (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHL (childHL (childHH (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL (childHH (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childHL (childHH (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL (childHH (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childHH (childHH (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childHH (childHH (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH (childHH (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childHH (childHH (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH (childHH (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHL (childHH (childHH (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH (childHH (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childHH (childHH (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH (childHH (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111133011 :
    adaptiveCoverCheck 9 (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childLL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childLL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childLL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childLL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childLH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childLH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childLH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childLH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLL (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childLL (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childLL (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childLL (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childLL (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childHL (childLL (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childHL (childLL (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL (childLL (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childHL (childLL (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL (childLL (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHL (childHL (childLL (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL (childLL (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childHL (childLL (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL (childLL (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childHH (childLL (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childHH (childLL (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH (childLL (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childHH (childLL (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH (childLL (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHL (childHH (childLL (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH (childLL (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childHH (childLL (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH (childLL (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLH (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childLH (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childLH (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childLH (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childLH (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childHL (childLH (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childHL (childLH (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL (childLH (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childHL (childLH (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL (childLH (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHL (childHL (childLH (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL (childLH (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childHL (childLH (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL (childLH (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childHH (childLH (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childHH (childLH (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH (childLH (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childHH (childLH (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH (childLH (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHL (childHH (childLH (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH (childLH (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childHH (childLH (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH (childLH (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHL (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childLL (childHL (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childLL (childHL (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL (childHL (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childLL (childHL (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL (childHL (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHL (childLL (childHL (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL (childHL (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childLL (childHL (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL (childHL (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childLH (childHL (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childLH (childHL (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH (childHL (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childLH (childHL (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH (childHL (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHL (childLH (childHL (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH (childHL (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childLH (childHL (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH (childHL (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childHL (childHL (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childHL (childHL (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL (childHL (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childHL (childHL (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL (childHL (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHL (childHL (childHL (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL (childHL (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childHL (childHL (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL (childHL (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childHH (childHL (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childHH (childHL (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH (childHL (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childHH (childHL (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH (childHL (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHL (childHH (childHL (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH (childHL (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childHH (childHL (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH (childHL (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHH (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childLL (childHH (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childLL (childHH (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL (childHH (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childLL (childHH (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL (childHH (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHL (childLL (childHH (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL (childHH (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childLL (childHH (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL (childHH (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childLH (childHH (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childLH (childHH (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH (childHH (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childLH (childHH (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH (childHH (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHL (childLH (childHH (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH (childHH (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childLH (childHH (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH (childHH (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childHL (childHH (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childHL (childHH (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL (childHH (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childHL (childHH (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL (childHH (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHL (childHL (childHH (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL (childHH (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childHL (childHH (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL (childHH (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childHH (childHH (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childHH (childHH (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH (childHH (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childHH (childHH (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH (childHH (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHL (childHH (childHH (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH (childHH (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childHH (childHH (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH (childHH (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLL (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childLL (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childLL (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childLL (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childLL (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childHL (childLL (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childHL (childLL (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL (childLL (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childHL (childLL (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL (childLL (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHL (childHL (childLL (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL (childLL (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childHL (childLL (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL (childLL (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childHH (childLL (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childHH (childLL (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH (childLL (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childHH (childLL (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH (childLL (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHL (childHH (childLL (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH (childLL (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childHH (childLL (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH (childLL (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLH (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childLH (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childLH (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childLH (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childLH (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childHL (childLH (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childHL (childLH (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL (childLH (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childHL (childLH (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL (childLH (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHL (childHL (childLH (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL (childLH (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childHL (childLH (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL (childLH (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childHH (childLH (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childHH (childLH (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH (childLH (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childHH (childLH (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH (childLH (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHL (childHH (childLH (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH (childLH (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childHH (childLH (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH (childLH (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHL (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childLL (childHL (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childLL (childHL (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL (childHL (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childLL (childHL (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL (childHL (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHL (childLL (childHL (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL (childHL (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childLL (childHL (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL (childHL (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childLH (childHL (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childLH (childHL (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH (childHL (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childLH (childHL (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH (childHL (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHL (childLH (childHL (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH (childHL (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childLH (childHL (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH (childHL (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childHL (childHL (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childHL (childHL (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL (childHL (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childHL (childHL (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL (childHL (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHL (childHL (childHL (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL (childHL (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childHL (childHL (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL (childHL (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childHH (childHL (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childHH (childHL (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH (childHL (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childHH (childHL (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH (childHL (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHL (childHH (childHL (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH (childHL (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childHH (childHL (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH (childHL (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHH (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childLL (childHH (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childLL (childHH (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL (childHH (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childLL (childHH (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL (childHH (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHL (childLL (childHH (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL (childHH (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childLL (childHH (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL (childHH (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childLH (childHH (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childLH (childHH (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH (childHH (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childLH (childHH (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH (childHH (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHL (childLH (childHH (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH (childHH (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childLH (childHH (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH (childHH (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childHL (childHH (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childHL (childHH (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL (childHH (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childHL (childHH (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL (childHH (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHL (childHL (childHH (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL (childHH (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childHL (childHH (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL (childHH (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childHH (childHH (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childHH (childHH (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH (childHH (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childHH (childHH (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH (childHH (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHL (childHH (childHH (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH (childHH (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childHH (childHH (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH (childHH (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111133012 :
    adaptiveCoverCheck 9 (childHL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLL (childLL (childHL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childLL (childLL (childHL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childLL (childLL (childHL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childLL (childLL (childHL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childLL (childLL (childHL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childLL (childLL (childHL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childLL (childLL (childHL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childLL (childLL (childHL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childLL (childLL (childHL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLH (childLL (childHL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childLH (childLL (childHL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childLH (childLL (childHL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childLH (childLL (childHL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childLH (childLL (childHL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childLH (childLL (childHL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childLH (childLL (childHL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childLH (childLL (childHL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childLH (childLL (childHL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h))
        (by
          have h : ((childHL (childLL (childHL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childLL (childHL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLL (childLH (childHL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childLL (childLH (childHL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childLL (childLH (childHL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childLL (childLH (childHL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childLL (childLH (childHL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childLL (childLH (childHL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childLL (childLH (childHL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childLL (childLH (childHL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childLL (childLH (childHL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLH (childLH (childHL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childLH (childLH (childHL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childLH (childLH (childHL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childLH (childLH (childHL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childLH (childLH (childHL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childLH (childLH (childHL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childLH (childLH (childHL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childLH (childLH (childHL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childLH (childLH (childHL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h))
        (by
          have h : ((childHL (childLH (childHL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childLH (childHL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))
    (by
      have h : ((childHL (childHL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childHL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111133013 :
    adaptiveCoverCheck 9 (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLL (childLL (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childLL (childLL (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childLL (childLL (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childLL (childLL (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childLL (childLL (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childLL (childLL (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childLL (childLL (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childLL (childLL (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childLL (childLL (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLH (childLL (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childLH (childLL (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childLH (childLL (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childLH (childLL (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childLH (childLL (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childLH (childLL (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childLH (childLL (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childLH (childLL (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childLH (childLL (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h))
        (by
          have h : ((childHL (childLL (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childLL (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLL (childLH (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childLL (childLH (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childLL (childLH (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childLH (childLL (childLH (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childLH (childLL (childLH (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH (childLL (childLH (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childLH (childLL (childLH (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH (childLL (childLH (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHL (childLH (childLL (childLH (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH (childLL (childLH (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childLH (childLL (childLH (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH (childLL (childLH (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h))
            (by
              have h : ((childHL (childLL (childLH (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childLL (childLH (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childLL (childLH (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childLL (childLH (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLH (childLH (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childLL (childLH (childLH (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childLL (childLH (childLH (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL (childLH (childLH (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childLL (childLH (childLH (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL (childLH (childLH (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHL (childLL (childLH (childLH (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL (childLH (childLH (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childLL (childLH (childLH (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL (childLH (childLH (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childLH (childLH (childLH (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childLH (childLH (childLH (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH (childLH (childLH (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childLH (childLH (childLH (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH (childLH (childLH (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHL (childLH (childLH (childLH (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH (childLH (childLH (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childLH (childLH (childLH (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH (childLH (childLH (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h))
            (by
              have h : ((childHL (childLH (childLH (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childLH (childLH (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childLH (childLH (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childLH (childLH (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h))
        (by
          have h : ((childHL (childLH (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childLH (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))
    (by
      have h : ((childHL (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111133100 :
    adaptiveCoverCheck 9 (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childLL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childLL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childLL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childLL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childLH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childLH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childLH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childLH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLL (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childLL (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childLL (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childLL (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childLL (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childHL (childLL (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childHL (childLL (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL (childLL (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childHL (childLL (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL (childLL (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHL (childHL (childLL (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL (childLL (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childHL (childLL (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL (childLL (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childHH (childLL (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childHH (childLL (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH (childLL (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childHH (childLL (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH (childLL (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHL (childHH (childLL (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH (childLL (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childHH (childLL (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH (childLL (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLH (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childLH (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childLH (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childLH (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childLH (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childLH (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childLH (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childLH (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childLH (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHL (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childLL (childHL (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childLL (childHL (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL (childHL (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childLL (childHL (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL (childHL (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHL (childLL (childHL (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL (childHL (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childLL (childHL (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childLH (childHL (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childLH (childHL (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH (childHL (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childLH (childHL (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH (childHL (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHL (childLH (childHL (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH (childHL (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childLH (childHL (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH (childHL (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childHL (childHL (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childHL (childHL (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL (childHL (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childHL (childHL (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL (childHL (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHL (childHL (childHL (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL (childHL (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childHL (childHL (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL (childHL (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childHH (childHL (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childHH (childHL (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH (childHL (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childHH (childHL (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH (childHL (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHL (childHH (childHL (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH (childHL (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childHH (childHL (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH (childHL (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHH (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childLL (childHH (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childLL (childHH (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL (childHH (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childLL (childHH (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL (childHH (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHL (childLL (childHH (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL (childHH (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childLL (childHH (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL (childHH (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childLH (childHH (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childLH (childHH (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH (childHH (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childLH (childHH (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH (childHH (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHL (childLH (childHH (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH (childHH (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childLH (childHH (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH (childHH (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childHL (childHH (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childHL (childHH (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL (childHH (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childHL (childHH (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL (childHH (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHL (childHL (childHH (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL (childHH (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childHL (childHH (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL (childHH (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childHH (childHH (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childHH (childHH (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH (childHH (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childHH (childHH (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH (childHH (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHL (childHH (childHH (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH (childHH (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childHH (childHH (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH (childHH (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLL (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childLL (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childLL (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childLL (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childLL (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childLL (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childLL (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childLL (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childLL (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childLH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childLH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childLH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childLH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childLH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childLH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childLH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childLH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHL (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childLL (childHL (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childLL (childHL (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL (childHL (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childLL (childHL (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL (childHL (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHL (childLL (childHL (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL (childHL (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childLL (childHL (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL (childHL (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childLH (childHL (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childLH (childHL (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH (childHL (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childLH (childHL (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH (childHL (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHL (childLH (childHL (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH (childHL (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childLH (childHL (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH (childHL (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childHL (childHL (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childHL (childHL (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL (childHL (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childHL (childHL (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL (childHL (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHL (childHL (childHL (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL (childHL (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childHL (childHL (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL (childHL (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childHH (childHL (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childHH (childHL (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH (childHL (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childHH (childHL (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH (childHL (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHH (childHL (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))
                    (by
                      have h : ((childLL (childHL (childHH (childHL (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHH (childHL (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childLH (childHL (childHH (childHL (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHH (childHL (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHL (childHL (childHH (childHL (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHH (childHL (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHH (childHL (childHH (childHL (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHH (childHL (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h))
                (by
                  exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHH (childHL (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))
                    (by
                      have h : ((childLL (childHH (childHH (childHL (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHH (childHL (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childLH (childHH (childHH (childHL (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHH (childHL (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHL (childHH (childHH (childHL (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHH (childHL (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHH (childHH (childHH (childHL (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHH (childHL (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h))))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childLL (childHH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childLL (childHH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL (childHH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childLL (childHH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL (childHH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHL (childLL (childHH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL (childHH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childLL (childHH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL (childHH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childLH (childHH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childLH (childHH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH (childHH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childLH (childHH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH (childHH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHL (childLH (childHH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH (childHH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  exact adaptiveCoverCheck_succ_of_children 4 (childHH (childLH (childHH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))
                    (by
                      have h : ((childLL (childHH (childLH (childHH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childLH (childHH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childLH (childHH (childLH (childHH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childLH (childHH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHL (childHH (childLH (childHH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childLH (childHH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHH (childHH (childLH (childHH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childLH (childHH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childHL (childHH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childHL (childHH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL (childHH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  exact adaptiveCoverCheck_succ_of_children 4 (childLH (childHL (childHH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))
                    (by
                      have h : ((childLL (childLH (childHL (childHH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childHL (childHH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childLH (childLH (childHL (childHH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childHL (childHH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHL (childLH (childHL (childHH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childHL (childHH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHH (childLH (childHL (childHH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childHL (childHH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h))
                (by
                  exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHL (childHH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))
                    (by
                      have h : ((childLL (childHL (childHL (childHH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHL (childHH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childLH (childHL (childHL (childHH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHL (childHH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHL (childHL (childHL (childHH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHL (childHH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHH (childHL (childHL (childHH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHL (childHH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h))
                (by
                  exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHL (childHH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))
                    (by
                      have h : ((childLL (childHH (childHL (childHH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHL (childHH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childLH (childHH (childHL (childHH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHL (childHH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHL (childHH (childHL (childHH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHL (childHH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHH (childHH (childHL (childHH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHL (childHH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childHH (childHH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  exact adaptiveCoverCheck_succ_of_children 4 (childLL (childHH (childHH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))
                    (by
                      have h : ((childLL (childLL (childHH (childHH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childHH (childHH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childLH (childLL (childHH (childHH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childHH (childHH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHL (childLL (childHH (childHH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childHH (childHH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHH (childLL (childHH (childHH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childHH (childHH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h))
                (by
                  exact adaptiveCoverCheck_succ_of_children 4 (childLH (childHH (childHH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))
                    (by
                      have h : ((childLL (childLH (childHH (childHH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childHH (childHH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childLH (childLH (childHH (childHH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childHH (childHH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHL (childLH (childHH (childHH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childHH (childHH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHH (childLH (childHH (childHH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childHH (childHH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h))
                (by
                  exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHH (childHH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))
                    (by
                      have h : ((childLL (childHL (childHH (childHH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHH (childHH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childLH (childHL (childHH (childHH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHH (childHH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHL (childHL (childHH (childHH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHH (childHH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHH (childHL (childHH (childHH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHH (childHH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h))
                (by
                  exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHH (childHH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))
                    (by
                      have h : ((childLL (childHH (childHH (childHH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHH (childHH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childLH (childHH (childHH (childHH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHH (childHH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHL (childHH (childHH (childHH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHH (childHH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHH (childHH (childHH (childHH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHH (childHH (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111133101 :
    adaptiveCoverCheck 9 (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childLL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childLL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childLL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childLL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childLH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childLH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childLH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childLH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childLL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childLL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childLL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childLL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childLL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childLL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childLL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childLL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childLH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childLH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childLH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childLH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childLH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childLH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childLH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childLH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childLL (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childLL (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childLL (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  exact adaptiveCoverCheck_succ_of_children 4 (childHL (childLL (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))
                    (by
                      have h : ((childLL (childHL (childLL (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childLL (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childLH (childHL (childLL (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childLL (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHL (childHL (childLL (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childLL (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHH (childHL (childLL (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childLL (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h))
                (by
                  exact adaptiveCoverCheck_succ_of_children 4 (childHH (childLL (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))
                    (by
                      have h : ((childLL (childHH (childLL (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childLL (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childLH (childHH (childLL (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childLL (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHL (childHH (childLL (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childLL (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHH (childHH (childLL (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childLL (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childLH (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childLH (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childLH (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  exact adaptiveCoverCheck_succ_of_children 4 (childHL (childLH (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))
                    (by
                      have h : ((childLL (childHL (childLH (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childLH (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childLH (childHL (childLH (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childLH (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHL (childHL (childLH (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childLH (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHH (childHL (childLH (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childLH (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h))
                (by
                  exact adaptiveCoverCheck_succ_of_children 4 (childHH (childLH (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))
                    (by
                      have h : ((childLL (childHH (childLH (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childLH (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childLH (childHH (childLH (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childLH (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHL (childHH (childLH (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childLH (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHH (childHH (childLH (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childLH (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childHL (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  exact adaptiveCoverCheck_succ_of_children 4 (childLL (childHL (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))
                    (by
                      have h : ((childLL (childLL (childHL (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childHL (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childLH (childLL (childHL (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childHL (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHL (childLL (childHL (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childHL (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHH (childLL (childHL (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childHL (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h))
                (by
                  exact adaptiveCoverCheck_succ_of_children 4 (childLH (childHL (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))
                    (by
                      have h : ((childLL (childLH (childHL (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childHL (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childLH (childLH (childHL (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childHL (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHL (childLH (childHL (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childHL (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHH (childLH (childHL (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childHL (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h))
                (by
                  exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHL (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))
                    (by
                      have h : ((childLL (childHL (childHL (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHL (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childLH (childHL (childHL (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHL (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHL (childHL (childHL (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHL (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHH (childHL (childHL (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHL (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h))
                (by
                  exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHL (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))
                    (by
                      have h : ((childLL (childHH (childHL (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHL (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childLH (childHH (childHL (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHL (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHL (childHH (childHL (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHL (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHH (childHH (childHL (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHL (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childHH (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  exact adaptiveCoverCheck_succ_of_children 4 (childLL (childHH (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))
                    (by
                      have h : ((childLL (childLL (childHH (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childHH (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childLH (childLL (childHH (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childHH (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHL (childLL (childHH (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childHH (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHH (childLL (childHH (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childHH (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h))
                (by
                  exact adaptiveCoverCheck_succ_of_children 4 (childLH (childHH (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))
                    (by
                      have h : ((childLL (childLH (childHH (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childHH (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childLH (childLH (childHH (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childHH (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHL (childLH (childHH (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childHH (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHH (childLH (childHH (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childHH (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h))
                (by
                  exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHH (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))
                    (by
                      have h : ((childLL (childHL (childHH (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHH (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childLH (childHL (childHH (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHH (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHL (childHL (childHH (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHH (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHH (childHL (childHH (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHH (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h))
                (by
                  exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHH (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))
                    (by
                      have h : ((childLL (childHH (childHH (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHH (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childLH (childHH (childHH (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHH (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHL (childHH (childHH (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHH (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHH (childHH (childHH (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHH (childHL (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h))))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childLL (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childLL (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childLL (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  exact adaptiveCoverCheck_succ_of_children 4 (childHL (childLL (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))
                    (by
                      have h : ((childLL (childHL (childLL (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childLL (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childLH (childHL (childLL (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childLL (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHL (childHL (childLL (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childLL (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHH (childHL (childLL (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childLL (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h))
                (by
                  exact adaptiveCoverCheck_succ_of_children 4 (childHH (childLL (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))
                    (by
                      have h : ((childLL (childHH (childLL (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childLL (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childLH (childHH (childLL (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childLL (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHL (childHH (childLL (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childLL (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHH (childHH (childLL (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childLL (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childLH (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childLH (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childLH (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHL (childLH (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childLH (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childHL (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  exact adaptiveCoverCheck_succ_of_children 4 (childLL (childHL (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))
                    (by
                      have h : ((childLL (childLL (childHL (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childHL (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childLH (childLL (childHL (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childHL (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHL (childLL (childHL (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childHL (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHH (childLL (childHL (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childHL (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h))
                (by
                  exact adaptiveCoverCheck_succ_of_children 4 (childLH (childHL (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))
                    (by
                      have h : ((childLL (childLH (childHL (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childHL (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childLH (childLH (childHL (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childHL (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHL (childLH (childHL (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childHL (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHH (childLH (childHL (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childHL (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h))
                (by
                  exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHL (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))
                    (by
                      have h : ((childLL (childHL (childHL (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHL (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childLH (childHL (childHL (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHL (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHL (childHL (childHL (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHL (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHH (childHL (childHL (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHL (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h))
                (by
                  exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHL (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))
                    (by
                      have h : ((childLL (childHH (childHL (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHL (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childLH (childHH (childHL (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHL (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHL (childHH (childHL (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHL (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHH (childHH (childHL (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHL (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childHH (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  exact adaptiveCoverCheck_succ_of_children 4 (childLL (childHH (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))
                    (by
                      have h : ((childLL (childLL (childHH (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childHH (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childLH (childLL (childHH (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childHH (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHL (childLL (childHH (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childHH (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHH (childLL (childHH (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childHH (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h))
                (by
                  exact adaptiveCoverCheck_succ_of_children 4 (childLH (childHH (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))
                    (by
                      have h : ((childLL (childLH (childHH (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childHH (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childLH (childLH (childHH (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childHH (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHL (childLH (childHH (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childHH (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHH (childLH (childHH (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childHH (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h))
                (by
                  exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHH (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))
                    (by
                      have h : ((childLL (childHL (childHH (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHH (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childLH (childHL (childHH (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHH (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHL (childHL (childHH (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHH (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHH (childHL (childHH (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHH (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h))
                (by
                  exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHH (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))
                    (by
                      have h : ((childLL (childHH (childHH (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHH (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childLH (childHH (childHH (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHH (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHL (childHH (childHH (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHH (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHH (childHH (childHH (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHH (childHH (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childLL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childLL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childLL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childLL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childLL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childLL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childLL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childLL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childLH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childLH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childLH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childLH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childLH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childLH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childLH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childLH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childLL (childHL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childLL (childHL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL (childHL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childLL (childHL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL (childHL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHL (childLL (childHL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL (childHL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childLL (childHL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL (childHL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childLH (childHL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childLH (childHL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH (childHL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childLH (childHL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH (childHL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHL (childLH (childHL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH (childHL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childLH (childHL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH (childHL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childHL (childHL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  exact adaptiveCoverCheck_succ_of_children 4 (childLL (childHL (childHL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))
                    (by
                      have h : ((childLL (childLL (childHL (childHL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childHL (childHL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childLH (childLL (childHL (childHL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childHL (childHL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHL (childLL (childHL (childHL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childHL (childHL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHH (childLL (childHL (childHL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childHL (childHL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h))
                (by
                  exact adaptiveCoverCheck_succ_of_children 4 (childLH (childHL (childHL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))
                    (by
                      have h : ((childLL (childLH (childHL (childHL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childHL (childHL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childLH (childLH (childHL (childHL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childHL (childHL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHL (childLH (childHL (childHL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childHL (childHL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHH (childLH (childHL (childHL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childHL (childHL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h))
                (by
                  exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHL (childHL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))
                    (by
                      have h : ((childLL (childHL (childHL (childHL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHL (childHL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childLH (childHL (childHL (childHL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHL (childHL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHL (childHL (childHL (childHL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHL (childHL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHH (childHL (childHL (childHL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHL (childHL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h))
                (by
                  exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHL (childHL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))
                    (by
                      have h : ((childLL (childHH (childHL (childHL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHL (childHL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childLH (childHH (childHL (childHL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHL (childHL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHL (childHH (childHL (childHL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHL (childHL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHH (childHH (childHL (childHL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHL (childHL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childHH (childHL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  exact adaptiveCoverCheck_succ_of_children 4 (childLL (childHH (childHL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))
                    (by
                      have h : ((childLL (childLL (childHH (childHL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childHH (childHL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childLH (childLL (childHH (childHL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childHH (childHL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHL (childLL (childHH (childHL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childHH (childHL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHH (childLL (childHH (childHL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childHH (childHL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h))
                (by
                  exact adaptiveCoverCheck_succ_of_children 4 (childLH (childHH (childHL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))
                    (by
                      have h : ((childLL (childLH (childHH (childHL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childHH (childHL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childLH (childLH (childHH (childHL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childHH (childHL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHL (childLH (childHH (childHL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childHH (childHL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHH (childLH (childHH (childHL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childHH (childHL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h))
                (by
                  exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHH (childHL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))
                    (by
                      have h : ((childLL (childHL (childHH (childHL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHH (childHL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childLH (childHL (childHH (childHL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHH (childHL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHL (childHL (childHH (childHL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHH (childHL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHH (childHL (childHH (childHL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHH (childHL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h))
                (by
                  exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHH (childHL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))
                    (by
                      have h : ((childLL (childHH (childHH (childHL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHH (childHL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childLH (childHH (childHH (childHL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHH (childHL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHL (childHH (childHH (childHL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHH (childHL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHH (childHH (childHH (childHL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHH (childHL (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h))))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childLL (childHH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childLL (childHH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL (childHH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childLL (childHH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL (childHH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHL (childLL (childHH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL (childHH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childLL (childHH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL (childHH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childLH (childHH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childLH (childHH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH (childHH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childLH (childHH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH (childHH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHL (childLH (childHH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH (childHH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childLH (childHH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH (childHH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childHL (childHH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  exact adaptiveCoverCheck_succ_of_children 4 (childLL (childHL (childHH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))
                    (by
                      have h : ((childLL (childLL (childHL (childHH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childHL (childHH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childLH (childLL (childHL (childHH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childHL (childHH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHL (childLL (childHL (childHH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childHL (childHH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHH (childLL (childHL (childHH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childHL (childHH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h))
                (by
                  exact adaptiveCoverCheck_succ_of_children 4 (childLH (childHL (childHH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))
                    (by
                      have h : ((childLL (childLH (childHL (childHH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childHL (childHH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childLH (childLH (childHL (childHH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childHL (childHH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHL (childLH (childHL (childHH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childHL (childHH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHH (childLH (childHL (childHH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childHL (childHH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h))
                (by
                  exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHL (childHH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))
                    (by
                      have h : ((childLL (childHL (childHL (childHH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHL (childHH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childLH (childHL (childHL (childHH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHL (childHH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHL (childHL (childHL (childHH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHL (childHH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHH (childHL (childHL (childHH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHL (childHH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h))
                (by
                  exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHL (childHH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))
                    (by
                      have h : ((childLL (childHH (childHL (childHH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHL (childHH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childLH (childHH (childHL (childHH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHL (childHH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHL (childHH (childHL (childHH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHL (childHH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHH (childHH (childHL (childHH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHL (childHH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childHH (childHH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  exact adaptiveCoverCheck_succ_of_children 4 (childLL (childHH (childHH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))
                    (by
                      have h : ((childLL (childLL (childHH (childHH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childHH (childHH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childLH (childLL (childHH (childHH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childHH (childHH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHL (childLL (childHH (childHH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childHH (childHH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHH (childLL (childHH (childHH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childHH (childHH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h))
                (by
                  exact adaptiveCoverCheck_succ_of_children 4 (childLH (childHH (childHH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))
                    (by
                      have h : ((childLL (childLH (childHH (childHH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childHH (childHH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childLH (childLH (childHH (childHH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childHH (childHH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHL (childLH (childHH (childHH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childHH (childHH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHH (childLH (childHH (childHH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childHH (childHH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h))
                (by
                  exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHH (childHH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))
                    (by
                      have h : ((childLL (childHL (childHH (childHH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHH (childHH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childLH (childHL (childHH (childHH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHH (childHH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHL (childHL (childHH (childHH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHH (childHH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHH (childHL (childHH (childHH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHH (childHH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h))
                (by
                  exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHH (childHH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))
                    (by
                      have h : ((childLL (childHH (childHH (childHH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHH (childHH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childLH (childHH (childHH (childHH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHH (childHH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHL (childHH (childHH (childHH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHH (childHH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHH (childHH (childHH (childHH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHH (childHH (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111133102 :
    adaptiveCoverCheck 9 (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLL (childLL (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childLL (childLL (childLL (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childLL (childLL (childLL (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL (childLL (childLL (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childLL (childLL (childLL (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL (childLL (childLL (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHL (childLL (childLL (childLL (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL (childLL (childLL (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childLL (childLL (childLL (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL (childLL (childLL (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childLH (childLL (childLL (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childLH (childLL (childLL (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH (childLL (childLL (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childLH (childLL (childLL (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH (childLL (childLL (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHL (childLH (childLL (childLL (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH (childLL (childLL (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childLH (childLL (childLL (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH (childLL (childLL (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h))
            (by
              have h : ((childHL (childLL (childLL (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childLL (childLL (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childLL (childLL (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childLL (childLL (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLH (childLL (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childLL (childLH (childLL (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childLL (childLH (childLL (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL (childLH (childLL (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childLL (childLH (childLL (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL (childLH (childLL (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHL (childLL (childLH (childLL (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL (childLH (childLL (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childLL (childLH (childLL (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL (childLH (childLL (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childLH (childLH (childLL (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childLH (childLH (childLL (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH (childLH (childLL (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childLH (childLH (childLL (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH (childLH (childLL (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHL (childLH (childLH (childLL (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH (childLH (childLL (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childLH (childLH (childLL (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH (childLH (childLL (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h))
            (by
              have h : ((childHL (childLH (childLL (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childLH (childLL (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childLH (childLL (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childLH (childLL (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h))
        (by
          have h : ((childHL (childLL (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childLL (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLL (childLH (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childLL (childLL (childLH (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childLL (childLL (childLH (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL (childLL (childLH (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childLL (childLL (childLH (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL (childLL (childLH (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHL (childLL (childLL (childLH (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL (childLL (childLH (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childLL (childLL (childLH (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL (childLL (childLH (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childLH (childLL (childLH (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childLH (childLL (childLH (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH (childLL (childLH (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childLH (childLL (childLH (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH (childLL (childLH (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHL (childLH (childLL (childLH (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH (childLL (childLH (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childLH (childLL (childLH (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH (childLL (childLH (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h))
            (by
              have h : ((childHL (childLL (childLH (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childLL (childLH (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childLL (childLH (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childLL (childLH (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLH (childLH (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childLL (childLH (childLH (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childLL (childLH (childLH (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL (childLH (childLH (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childLL (childLH (childLH (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL (childLH (childLH (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHL (childLL (childLH (childLH (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL (childLH (childLH (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childLL (childLH (childLH (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL (childLH (childLH (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childLH (childLH (childLH (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childLH (childLH (childLH (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH (childLH (childLH (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childLH (childLH (childLH (childLH (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH (childLH (childLH (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHL (childLH (childLH (childLH (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH (childLH (childLH (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childLH (childLH (childLH (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH (childLH (childLH (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h))
            (by
              have h : ((childHL (childLH (childLH (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childLH (childLH (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childLH (childLH (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childLH (childLH (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h))
        (by
          have h : ((childHL (childLH (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childLH (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))
    (by
      have h : ((childHL (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111133103 :
    adaptiveCoverCheck 9 (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLL (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childLL (childLL (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  have h : ((childLL (childLL (childLL (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL (childLL (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLL (childLL (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))
                    (by
                      have h : ((childLL (childLH (childLL (childLL (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLL (childLL (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childLH (childLH (childLL (childLL (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLL (childLL (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHL (childLH (childLL (childLL (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLL (childLL (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHH (childLH (childLL (childLL (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLL (childLL (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h))
                (by
                  have h : ((childHL (childLL (childLL (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL (childLL (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childLL (childLL (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL (childLL (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childLH (childLL (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLH (childLL (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))
                    (by
                      have h : ((childLL (childLL (childLH (childLL (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLH (childLL (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childLH (childLL (childLH (childLL (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLH (childLL (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHL (childLL (childLH (childLL (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLH (childLL (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHH (childLL (childLH (childLL (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLH (childLL (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h))
                (by
                  exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLH (childLL (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))
                    (by
                      have h : ((childLL (childLH (childLH (childLL (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLH (childLL (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childLH (childLH (childLH (childLL (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLH (childLL (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHL (childLH (childLH (childLL (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLH (childLL (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHH (childLH (childLH (childLL (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLH (childLL (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h))
                (by
                  have h : ((childHL (childLH (childLL (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH (childLL (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childLH (childLL (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH (childLL (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h))
            (by
              have h : ((childHL (childLL (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childLL (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childLL (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childLL (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLH (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childLL (childLH (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLL (childLH (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))
                    (by
                      have h : ((childLL (childLL (childLL (childLH (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLL (childLH (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childLH (childLL (childLL (childLH (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLL (childLH (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHL (childLL (childLL (childLH (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLL (childLH (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHH (childLL (childLL (childLH (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLL (childLH (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h))
                (by
                  exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLL (childLH (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))
                    (by
                      have h : ((childLL (childLH (childLL (childLH (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLL (childLH (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childLH (childLH (childLL (childLH (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLL (childLH (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHL (childLH (childLL (childLH (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLL (childLH (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHH (childLH (childLL (childLH (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLL (childLH (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h))
                (by
                  have h : ((childHL (childLL (childLH (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL (childLH (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childLL (childLH (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL (childLH (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childLH (childLH (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLH (childLH (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))
                    (by
                      have h : ((childLL (childLL (childLH (childLH (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLH (childLH (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childLH (childLL (childLH (childLH (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLH (childLH (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHL (childLL (childLH (childLH (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLH (childLH (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHH (childLL (childLH (childLH (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLH (childLH (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h))
                (by
                  exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLH (childLH (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))
                    (by
                      have h : ((childLL (childLH (childLH (childLH (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLH (childLH (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childLH (childLH (childLH (childLH (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLH (childLH (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHL (childLH (childLH (childLH (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLH (childLH (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHH (childLH (childLH (childLH (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLH (childLH (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h))
                (by
                  have h : ((childHL (childLH (childLH (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH (childLH (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childLH (childLH (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH (childLH (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h))
            (by
              have h : ((childHL (childLH (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childLH (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childLH (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childLH (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h))
        (by
          have h : ((childHL (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLL (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childLL (childLL (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLL (childLL (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))
                    (by
                      have h : ((childLL (childLL (childLL (childLL (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLL (childLL (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childLH (childLL (childLL (childLL (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLL (childLL (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHL (childLL (childLL (childLL (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLL (childLL (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHH (childLL (childLL (childLL (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLL (childLL (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h))
                (by
                  exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLL (childLL (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))
                    (by
                      have h : ((childLL (childLH (childLL (childLL (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLL (childLL (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childLH (childLH (childLL (childLL (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLL (childLL (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHL (childLH (childLL (childLL (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLL (childLL (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHH (childLH (childLL (childLL (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLL (childLL (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h))
                (by
                  have h : ((childHL (childLL (childLL (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL (childLL (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childLL (childLL (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL (childLL (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childLH (childLL (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLH (childLL (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))
                    (by
                      have h : ((childLL (childLL (childLH (childLL (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLH (childLL (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childLH (childLL (childLH (childLL (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLH (childLL (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHL (childLL (childLH (childLL (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLH (childLL (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHH (childLL (childLH (childLL (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLH (childLL (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h))
                (by
                  exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLH (childLL (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))
                    (by
                      have h : ((childLL (childLH (childLH (childLL (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLH (childLL (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childLH (childLH (childLH (childLL (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLH (childLL (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHL (childLH (childLH (childLL (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLH (childLL (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHH (childLH (childLH (childLL (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLH (childLL (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h))
                (by
                  have h : ((childHL (childLH (childLL (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH (childLL (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childLH (childLL (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH (childLL (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h))
            (by
              have h : ((childHL (childLL (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childLL (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childLL (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childLL (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLH (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childLL (childLH (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLL (childLH (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))
                    (by
                      have h : ((childLL (childLL (childLL (childLH (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLL (childLH (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childLH (childLL (childLL (childLH (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLL (childLH (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHL (childLL (childLL (childLH (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLL (childLH (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHH (childLL (childLL (childLH (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLL (childLH (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h))
                (by
                  exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLL (childLH (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))
                    (by
                      have h : ((childLL (childLH (childLL (childLH (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLL (childLH (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childLH (childLH (childLL (childLH (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLL (childLH (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHL (childLH (childLL (childLH (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLL (childLH (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHH (childLH (childLL (childLH (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLL (childLH (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h))
                (by
                  have h : ((childHL (childLL (childLH (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL (childLH (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childLL (childLH (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL (childLH (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h))
            (by
              exact adaptiveCoverCheck_succ_of_children 5 (childLH (childLH (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))
                (by
                  exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLH (childLH (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))
                    (by
                      have h : ((childLL (childLL (childLH (childLH (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLH (childLH (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childLH (childLL (childLH (childLH (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLH (childLH (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHL (childLL (childLH (childLH (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLH (childLH (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHH (childLL (childLH (childLH (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLH (childLH (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h))
                (by
                  exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLH (childLH (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))
                    (by
                      have h : ((childLL (childLH (childLH (childLH (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLH (childLH (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childLH (childLH (childLH (childLH (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLH (childLH (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHL (childLH (childLH (childLH (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLH (childLH (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h)
                    (by
                      have h : ((childHH (childLH (childLH (childLH (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))))).rejected = true := by
                        decide +kernel
                      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLH (childLH (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))) h))
                (by
                  have h : ((childHL (childLH (childLH (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH (childLH (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h)
                (by
                  have h : ((childHH (childLH (childLH (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))))).rejected = true := by
                    decide +kernel
                  exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH (childLH (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))) h))
            (by
              have h : ((childHL (childLH (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childLH (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childLH (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childLH (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h))
        (by
          have h : ((childHL (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))
    (by
      have h : ((childHL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childHH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childHH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childHH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childHH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))

end PartE
end GerverSofa
