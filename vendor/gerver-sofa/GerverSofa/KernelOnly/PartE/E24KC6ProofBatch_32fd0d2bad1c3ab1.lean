import GerverSofa.KernelOnly.PartE.E24KC2ProofHelpers

/-! E24KC6 explicit proof-producing certificate batch. -/
noncomputable section

namespace GerverSofa
namespace PartE

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0000331021 :
    adaptiveCoverCheck 9 (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHL (childLL (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childHL (childLL (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHL (childLL (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childHL (childLL (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHL (childLL (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childHL (childLL (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHL (childLL (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childHL (childLL (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHL (childLL (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHH (childLL (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childHH (childLL (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHH (childLL (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childHH (childLL (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHH (childLL (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childHH (childLL (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHH (childLL (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childHH (childLL (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHH (childLL (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHL (childLH (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childHL (childLH (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHL (childLH (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childHL (childLH (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHL (childLH (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childHL (childLH (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHL (childLH (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childHL (childLH (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHL (childLH (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHH (childLH (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childHH (childLH (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHH (childLH (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childHH (childLH (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHH (childLH (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childHH (childLH (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHH (childLH (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childHH (childLH (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHH (childLH (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLL (childHL (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childLL (childHL (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childLL (childHL (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childLL (childHL (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childLL (childHL (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childLL (childHL (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childLL (childHL (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childLL (childHL (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childLL (childHL (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLH (childHL (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childLH (childHL (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childLH (childHL (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childLH (childHL (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childLH (childHL (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childLH (childHL (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childLH (childHL (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childLH (childHL (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childLH (childHL (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHL (childHL (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childHL (childHL (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHL (childHL (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childHL (childHL (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHL (childHL (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childHL (childHL (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHL (childHL (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childHL (childHL (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHL (childHL (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHH (childHL (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childHH (childHL (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHH (childHL (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childHH (childHL (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHH (childHL (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childHH (childHL (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHH (childHL (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childHH (childHL (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHH (childHL (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLL (childHH (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childLL (childHH (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childLL (childHH (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childLL (childHH (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childLL (childHH (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childLL (childHH (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childLL (childHH (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childLL (childHH (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childLL (childHH (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLH (childHH (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childLH (childHH (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childLH (childHH (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childLH (childHH (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childLH (childHH (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childLH (childHH (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childLH (childHH (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childLH (childHH (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childLH (childHH (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHL (childHH (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childHL (childHH (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHL (childHH (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childHL (childHH (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHL (childHH (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childHL (childHH (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHL (childHH (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childHL (childHH (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHL (childHH (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHH (childHH (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childHH (childHH (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHH (childHH (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childHH (childHH (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHH (childHH (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childHH (childHH (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHH (childHH (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childHH (childHH (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHH (childHH (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0000331022 :
    adaptiveCoverCheck 9 (childHL (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHL (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childHL (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childHL (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childHL (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childHL (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childHL (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHL (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childHL (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHL (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHL (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childHL (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childHL (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childHL (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childHL (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childHL (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHL (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childHL (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHL (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      have h : ((childHL (childHL (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0000331023 :
    adaptiveCoverCheck 9 (childHH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childHH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childHH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childHH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childHH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childHH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childHH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childHH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childHH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childHH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childHH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childHH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childHH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      have h : ((childHL (childHH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0000331030 :
    adaptiveCoverCheck 9 (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHL (childLL (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childHL (childLL (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHL (childLL (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childHL (childLL (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHL (childLL (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childHL (childLL (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHL (childLL (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childHL (childLL (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHL (childLL (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHH (childLL (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childHH (childLL (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHH (childLL (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childHH (childLL (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHH (childLL (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childHH (childLL (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHH (childLL (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childHH (childLL (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHH (childLL (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHL (childLH (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childHL (childLH (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHL (childLH (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childHL (childLH (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHL (childLH (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childHL (childLH (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHL (childLH (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childHL (childLH (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHL (childLH (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHH (childLH (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childHH (childLH (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHH (childLH (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childHH (childLH (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHH (childLH (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childHH (childLH (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHH (childLH (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childHH (childLH (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHH (childLH (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLL (childHL (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childLL (childHL (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childLL (childHL (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childLL (childHL (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childLL (childHL (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childLL (childHL (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childLL (childHL (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childLL (childHL (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childLL (childHL (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLH (childHL (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childLH (childHL (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childLH (childHL (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childLH (childHL (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childLH (childHL (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childLH (childHL (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childLH (childHL (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childLH (childHL (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childLH (childHL (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHL (childHL (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childHL (childHL (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHL (childHL (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childHL (childHL (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHL (childHL (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childHL (childHL (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHL (childHL (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childHL (childHL (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHL (childHL (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHH (childHL (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childHH (childHL (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHH (childHL (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childHH (childHL (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHH (childHL (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childHH (childHL (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHH (childHL (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childHH (childHL (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHH (childHL (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLL (childHH (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childLL (childHH (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childLL (childHH (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childLL (childHH (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childLL (childHH (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childLL (childHH (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childLL (childHH (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childLL (childHH (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childLL (childHH (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLH (childHH (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childLH (childHH (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childLH (childHH (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childLH (childHH (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childLH (childHH (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childLH (childHH (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childLH (childHH (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childLH (childHH (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childLH (childHH (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHL (childHH (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childHL (childHH (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHL (childHH (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childHL (childHH (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHL (childHH (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childHL (childHH (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHL (childHH (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childHL (childHH (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHL (childHH (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHH (childHH (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childHH (childHH (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHH (childHH (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childHH (childHH (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHH (childHH (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childHH (childHH (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHH (childHH (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childHH (childHH (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHH (childHH (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0000331031 :
    adaptiveCoverCheck 9 (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHL (childLL (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childHL (childLL (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHL (childLL (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childHL (childLL (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHL (childLL (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childHL (childLL (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHL (childLL (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childHL (childLL (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHL (childLL (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHH (childLL (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childHH (childLL (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHH (childLL (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childHH (childLL (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHH (childLL (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childHH (childLL (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHH (childLL (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childHH (childLL (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHH (childLL (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHL (childLH (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childHL (childLH (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHL (childLH (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childHL (childLH (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHL (childLH (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childHL (childLH (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHL (childLH (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childHL (childLH (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHL (childLH (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHH (childLH (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childHH (childLH (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHH (childLH (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childHH (childLH (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHH (childLH (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childHH (childLH (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHH (childLH (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childHH (childLH (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHH (childLH (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLL (childHL (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childLL (childHL (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childLL (childHL (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childLL (childHL (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childLL (childHL (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childLL (childHL (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childLL (childHL (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childLL (childHL (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childLL (childHL (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLH (childHL (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childLH (childHL (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childLH (childHL (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childLH (childHL (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childLH (childHL (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childLH (childHL (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childLH (childHL (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childLH (childHL (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childLH (childHL (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHL (childHL (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childHL (childHL (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHL (childHL (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childHL (childHL (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHL (childHL (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childHL (childHL (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHL (childHL (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childHL (childHL (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHL (childHL (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHH (childHL (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childHH (childHL (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHH (childHL (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childHH (childHL (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHH (childHL (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childHH (childHL (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHH (childHL (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childHH (childHL (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHH (childHL (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLL (childHH (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childLL (childHH (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childLL (childHH (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childLL (childHH (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childLL (childHH (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childLL (childHH (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childLL (childHH (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childLL (childHH (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childLL (childHH (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLH (childHH (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childLH (childHH (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childLH (childHH (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childLH (childHH (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childLH (childHH (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childLH (childHH (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childLH (childHH (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childLH (childHH (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childLH (childHH (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHL (childHH (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childHL (childHH (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHL (childHH (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childHL (childHH (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHL (childHH (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childHL (childHH (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHL (childHH (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childHL (childHH (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHL (childHH (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHH (childHH (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childHH (childHH (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHH (childHH (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childHH (childHH (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHH (childHH (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childHH (childHH (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHH (childHH (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childHH (childHH (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHH (childHH (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0000331032 :
    adaptiveCoverCheck 9 (childHL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childHL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childHL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childHL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childHL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childHL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childHL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childHL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childHL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childHL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childHL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childHL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childHL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      have h : ((childHL (childHL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0000331033 :
    adaptiveCoverCheck 9 (childHH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childHH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childHH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childHH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childHH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childHH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childHH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childHH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childHH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childHH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childHH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childHH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childHH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      have h : ((childHL (childHH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0000331102 :
    adaptiveCoverCheck 9 (childHL (childLL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childLL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childLL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childLL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childLL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childLL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childLL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childLL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childLL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childLL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0000331103 :
    adaptiveCoverCheck 9 (childHH (childLL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childLL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childLL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childLL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childLL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childLL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childLL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childLL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childLL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childLL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0000331112 :
    adaptiveCoverCheck 9 (childHL (childLH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childLH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childLH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childLH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childLH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childLH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childLH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childLH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childLH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childLH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0000331113 :
    adaptiveCoverCheck 9 (childHH (childLH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childLH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childLH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childLH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childLH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childLH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childLH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childLH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childLH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childLH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0000331120 :
    adaptiveCoverCheck 9 (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHL (childLL (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childHL (childLL (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHL (childLL (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childHL (childLL (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHL (childLL (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childHL (childLL (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHL (childLL (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childHL (childLL (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHL (childLL (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHH (childLL (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childHH (childLL (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHH (childLL (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childHH (childLL (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHH (childLL (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childHH (childLL (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHH (childLL (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childHH (childLL (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHH (childLL (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHL (childLH (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childHL (childLH (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHL (childLH (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childHL (childLH (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHL (childLH (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childHL (childLH (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHL (childLH (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childHL (childLH (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHL (childLH (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHH (childLH (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childHH (childLH (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHH (childLH (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childHH (childLH (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHH (childLH (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childHH (childLH (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHH (childLH (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childHH (childLH (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHH (childLH (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLL (childHL (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childLL (childHL (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childLL (childHL (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childLL (childHL (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childLL (childHL (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childLL (childHL (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childLL (childHL (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childLL (childHL (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childLL (childHL (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLH (childHL (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childLH (childHL (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childLH (childHL (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childLH (childHL (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childLH (childHL (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childLH (childHL (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childLH (childHL (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childLH (childHL (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childLH (childHL (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHL (childHL (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childHL (childHL (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHL (childHL (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childHL (childHL (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHL (childHL (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childHL (childHL (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHL (childHL (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childHL (childHL (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHL (childHL (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHH (childHL (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childHH (childHL (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHH (childHL (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childHH (childHL (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHH (childHL (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childHH (childHL (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHH (childHL (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childHH (childHL (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHH (childHL (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLL (childHH (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childLL (childHH (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childLL (childHH (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childLL (childHH (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childLL (childHH (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childLL (childHH (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childLL (childHH (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childLL (childHH (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childLL (childHH (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLH (childHH (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childLH (childHH (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childLH (childHH (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childLH (childHH (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childLH (childHH (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childLH (childHH (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childLH (childHH (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childLH (childHH (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childLH (childHH (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHL (childHH (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childHL (childHH (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHL (childHH (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childHL (childHH (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHL (childHH (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childHL (childHH (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHL (childHH (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childHL (childHH (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHL (childHH (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHH (childHH (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childHH (childHH (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHH (childHH (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childHH (childHH (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHH (childHH (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childHH (childHH (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHH (childHH (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childHH (childHH (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHH (childHH (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0000331121 :
    adaptiveCoverCheck 9 (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHL (childLL (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childHL (childLL (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHL (childLL (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childHL (childLL (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHL (childLL (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childHL (childLL (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHL (childLL (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childHL (childLL (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHL (childLL (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHH (childLL (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childHH (childLL (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHH (childLL (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childHH (childLL (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHH (childLL (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childHH (childLL (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHH (childLL (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childHH (childLL (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHH (childLL (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHL (childLH (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childHL (childLH (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHL (childLH (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childHL (childLH (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHL (childLH (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childHL (childLH (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHL (childLH (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childHL (childLH (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHL (childLH (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHH (childLH (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childHH (childLH (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHH (childLH (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childHH (childLH (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHH (childLH (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childHH (childLH (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHH (childLH (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childHH (childLH (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHH (childLH (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLL (childHL (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childLL (childHL (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childLL (childHL (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childLL (childHL (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childLL (childHL (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childLL (childHL (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childLL (childHL (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childLL (childHL (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childLL (childHL (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLH (childHL (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childLH (childHL (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childLH (childHL (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childLH (childHL (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childLH (childHL (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childLH (childHL (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childLH (childHL (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childLH (childHL (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childLH (childHL (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHL (childHL (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childHL (childHL (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHL (childHL (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childHL (childHL (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHL (childHL (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childHL (childHL (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHL (childHL (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childHL (childHL (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHL (childHL (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHH (childHL (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childHH (childHL (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHH (childHL (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childHH (childHL (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHH (childHL (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childHH (childHL (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHH (childHL (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childHH (childHL (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHH (childHL (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLL (childHH (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childLL (childHH (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childLL (childHH (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childLL (childHH (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childLL (childHH (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childLL (childHH (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childLL (childHH (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childLL (childHH (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childLL (childHH (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLH (childHH (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childLH (childHH (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childLH (childHH (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childLH (childHH (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childLH (childHH (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childLH (childHH (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childLH (childHH (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childLH (childHH (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childLH (childHH (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h))
        (by
          have h : ((childHL (childHH (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHH (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0000331122 :
    adaptiveCoverCheck 9 (childHL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childHL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childHL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childHL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childHL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childHL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childHL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childHL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childHL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childHL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childHL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childHL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childHL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      have h : ((childHL (childHL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0000331123 :
    adaptiveCoverCheck 9 (childHH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childHH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childHH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childHH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childHH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childHH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childHH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childHH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childHH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childHH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childHH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childHH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childHH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      have h : ((childHL (childHH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0000331130 :
    adaptiveCoverCheck 9 (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHL (childLL (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childHL (childLL (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHL (childLL (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childHL (childLL (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHL (childLL (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childHL (childLL (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHL (childLL (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childHL (childLL (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHL (childLL (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHH (childLL (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childHH (childLL (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHH (childLL (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childHH (childLL (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHH (childLL (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childHH (childLL (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHH (childLL (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childHH (childLL (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHH (childLL (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childHL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childHL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childHL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childHL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHL (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHH (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childHH (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHH (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childHH (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHH (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childHH (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHH (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childHH (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHH (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLL (childHL (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childLL (childHL (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childLL (childHL (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childLL (childHL (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childLL (childHL (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childLL (childHL (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childLL (childHL (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childLL (childHL (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childLL (childHL (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLH (childHL (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childLH (childHL (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childLH (childHL (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childLH (childHL (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childLH (childHL (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childLH (childHL (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childLH (childHL (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childLH (childHL (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childLH (childHL (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h))
        (by
          have h : ((childHL (childHL (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHL (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLL (childHH (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childLL (childHH (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childLL (childHH (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childLL (childHH (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childLL (childHH (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childLL (childHH (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childLL (childHH (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childLL (childHH (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childLL (childHH (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLH (childHH (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childLH (childHH (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childLH (childHH (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childLH (childHH (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childLH (childHH (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childLH (childHH (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childLH (childHH (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childLH (childHH (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childLH (childHH (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h))
        (by
          have h : ((childHL (childHH (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHH (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0000331131 :
    adaptiveCoverCheck 9 (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHL (childLL (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childHL (childLL (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHL (childLL (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childHL (childLL (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHL (childLL (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childHL (childLL (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHL (childLL (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childHL (childLL (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHL (childLL (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHH (childLL (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childHH (childLL (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHH (childLL (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childHH (childLL (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHH (childLL (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childHH (childLL (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHH (childLL (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childHH (childLL (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHH (childLL (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childHL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childHL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childHL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childHL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHL (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childHH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childHH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childHH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childHH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHH (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLL (childHL (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childLL (childHL (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childLL (childHL (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childLL (childHL (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childLL (childHL (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childLL (childHL (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childLL (childHL (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childLL (childHL (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childLL (childHL (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLH (childHL (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childLH (childHL (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childLH (childHL (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childLH (childHL (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childLH (childHL (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childLH (childHL (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childLH (childHL (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childLH (childHL (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childLH (childHL (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h))
        (by
          have h : ((childHL (childHL (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHL (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLL (childHH (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childLL (childHH (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childLL (childHH (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childLL (childHH (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childLL (childHH (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childLL (childHH (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childLL (childHH (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childLL (childHH (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childLL (childHH (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLH (childHH (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childLH (childHH (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childLH (childHH (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childLH (childHH (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childLH (childHH (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childLH (childHH (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childLH (childHH (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childLH (childHH (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childLH (childHH (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h))
        (by
          have h : ((childHL (childHH (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHH (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0000331132 :
    adaptiveCoverCheck 9 (childHL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childHL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childHL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childHL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childHL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childHL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childHL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childHL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childHL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childHL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childHL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childHL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childHL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      have h : ((childHL (childHL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0000331133 :
    adaptiveCoverCheck 9 (childHH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childHH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childHH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childHH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childHH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childHH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childHH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childHH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childHH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childHH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childHH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childHH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childHH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      have h : ((childHL (childHH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001220002 :
    adaptiveCoverCheck 9 (childHL (childLL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childLL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childLL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childLL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childLL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childLL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childLL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childLL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childLL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childLL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001220003 :
    adaptiveCoverCheck 9 (childHH (childLL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childLL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childLL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childLL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childLL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childLL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childLL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childLL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childLL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childLL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001220012 :
    adaptiveCoverCheck 9 (childHL (childLH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childLH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childLH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childLH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childLH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childLH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childLH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childLH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childLH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childLH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001220013 :
    adaptiveCoverCheck 9 (childHH (childLH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childLH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childLH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childLH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childLH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childLH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childLH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childLH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childLH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childLH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001220020 :
    adaptiveCoverCheck 9 (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHL (childLL (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childHL (childLL (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHL (childLL (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childHL (childLL (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHL (childLL (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childHL (childLL (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHL (childLL (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childHL (childLL (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHL (childLL (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHH (childLL (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childHH (childLL (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHH (childLL (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childHH (childLL (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHH (childLL (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childHH (childLL (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHH (childLL (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childHH (childLL (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHH (childLL (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHL (childLH (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childHL (childLH (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHL (childLH (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childHL (childLH (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHL (childLH (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childHL (childLH (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHL (childLH (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childHL (childLH (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHL (childLH (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHH (childLH (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childHH (childLH (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHH (childLH (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childHH (childLH (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHH (childLH (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childHH (childLH (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHH (childLH (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childHH (childLH (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHH (childLH (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLL (childHL (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childLL (childHL (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childLL (childHL (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childLL (childHL (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childLL (childHL (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childLL (childHL (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childLL (childHL (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childLL (childHL (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childLL (childHL (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLH (childHL (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childLH (childHL (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childLH (childHL (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childLH (childHL (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childLH (childHL (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childLH (childHL (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childLH (childHL (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childLH (childHL (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childLH (childHL (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h))
        (by
          have h : ((childHL (childHL (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHL (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLL (childHH (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childLL (childHH (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childLL (childHH (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childLL (childHH (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childLL (childHH (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childLL (childHH (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childLL (childHH (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childLL (childHH (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childLL (childHH (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLH (childHH (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childLH (childHH (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childLH (childHH (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childLH (childHH (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childLH (childHH (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childLH (childHH (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childLH (childHH (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childLH (childHH (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childLH (childHH (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h))
        (by
          have h : ((childHL (childHH (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHH (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001220021 :
    adaptiveCoverCheck 9 (childLH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childHL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childHL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childHL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childHL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHL (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHH (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childHH (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHH (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childHH (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHH (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childHH (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHH (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childHH (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHH (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childHL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childHL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childHL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childHL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHL (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHH (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childHH (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHH (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childHH (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHH (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childHH (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHH (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childHH (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHH (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLL (childHL (childLH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childLL (childHL (childLH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childLL (childHL (childLH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childLL (childHL (childLH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childLL (childHL (childLH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childLL (childHL (childLH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childLL (childHL (childLH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childLL (childHL (childLH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childLL (childHL (childLH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h))
        (by
          have h : ((childLH (childHL (childLH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHL (childLH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHL (childLH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHH (childLH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHH (childLH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHH (childLH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHH (childLH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001220022 :
    adaptiveCoverCheck 9 (childHL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childHL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childHL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childHL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childHL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childHL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childHL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childHL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childHL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childHL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childHL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childHL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childHL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      have h : ((childHL (childHL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001220023 :
    adaptiveCoverCheck 9 (childHH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childHH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childHH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childHH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childHH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childHH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childHH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childHH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childHH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childHH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childHH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childHH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childHH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      have h : ((childHL (childHH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001220030 :
    adaptiveCoverCheck 9 (childLL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childLL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childLL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childLL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childLL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHL (childLL (childLL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childHL (childLL (childLL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHL (childLL (childLL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childHL (childLL (childLL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHL (childLL (childLL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childHL (childLL (childLL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHL (childLL (childLL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childHL (childLL (childLL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHL (childLL (childLL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHH (childLL (childLL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childHH (childLL (childLL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHH (childLL (childLL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childHH (childLL (childLL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHH (childLL (childLL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childHH (childLL (childLL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHH (childLL (childLL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childHH (childLL (childLL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHH (childLL (childLL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childLL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childLL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childLL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childLL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHL (childLH (childLL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childHL (childLH (childLL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHL (childLH (childLL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childHL (childLH (childLL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHL (childLH (childLL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childHL (childLH (childLL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHL (childLH (childLL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childHL (childLH (childLL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHL (childLH (childLL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHH (childLH (childLL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childHH (childLH (childLL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHH (childLH (childLL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childHH (childLH (childLL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHH (childLH (childLL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childHH (childLH (childLL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHH (childLH (childLL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childHH (childLH (childLL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHH (childLH (childLL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHL (childLL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childLL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHL (childLL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHL (childLL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHL (childLL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHH (childLL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHH (childLL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHH (childLL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHH (childLL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001220031 :
    adaptiveCoverCheck 9 (childLH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childLH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childLH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childLH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childLH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHL (childLL (childLH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childHL (childLL (childLH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHL (childLL (childLH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childHL (childLL (childLH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHL (childLL (childLH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childHL (childLL (childLH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHL (childLL (childLH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childHL (childLL (childLH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHL (childLL (childLH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHH (childLL (childLH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childHH (childLL (childLH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHH (childLL (childLH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childHH (childLL (childLH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHH (childLL (childLH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childHH (childLL (childLH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHH (childLL (childLH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childHH (childLL (childLH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHH (childLL (childLH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childLH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childLH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childLH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childLH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHL (childLH (childLH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childHL (childLH (childLH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHL (childLH (childLH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childHL (childLH (childLH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHL (childLH (childLH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childHL (childLH (childLH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHL (childLH (childLH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childHL (childLH (childLH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHL (childLH (childLH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHH (childLH (childLH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childHH (childLH (childLH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHH (childLH (childLH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childHH (childLH (childLH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHH (childLH (childLH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childHH (childLH (childLH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHH (childLH (childLH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childHH (childLH (childLH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHH (childLH (childLH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHL (childLH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childLH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHL (childLH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHL (childLH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHL (childLH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHH (childLH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHH (childLH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHH (childLH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHH (childLH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001220032 :
    adaptiveCoverCheck 9 (childHL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childHL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childHL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childHL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childHL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childHL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childHL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childHL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childHL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childHL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childHL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childHL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childHL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      have h : ((childHL (childHL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001220033 :
    adaptiveCoverCheck 9 (childHH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childHH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childHH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childHH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childHH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childHH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childHH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childHH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childHH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childHH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childHH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childHH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childHH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      have h : ((childHL (childHH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001220102 :
    adaptiveCoverCheck 9 (childHL (childLL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childLL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childLL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childLL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childLL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childLL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childLL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childLL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childLL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childLL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001220103 :
    adaptiveCoverCheck 9 (childHH (childLL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childLL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childLL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childLL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childLL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childLL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childLL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childLL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childLL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childLL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001220112 :
    adaptiveCoverCheck 9 (childHL (childLH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childLH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childLH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childLH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childLH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childLH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childLH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childLH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childLH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childLH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001220113 :
    adaptiveCoverCheck 9 (childHH (childLH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childLH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childLH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childLH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childLH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childLH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childLH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childLH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childLH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childLH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001220120 :
    adaptiveCoverCheck 9 (childLL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childLL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childLL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childLL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childLL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHL (childLL (childLL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childHL (childLL (childLL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHL (childLL (childLL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childHL (childLL (childLL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHL (childLL (childLL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childHL (childLL (childLL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHL (childLL (childLL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childHL (childLL (childLL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHL (childLL (childLL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHH (childLL (childLL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childHH (childLL (childLL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHH (childLL (childLL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childHH (childLL (childLL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHH (childLL (childLL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childHH (childLL (childLL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHH (childLL (childLL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childHH (childLL (childLL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHH (childLL (childLL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childLL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childLL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childLL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childLL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHL (childLH (childLL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childHL (childLH (childLL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHL (childLH (childLL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childHL (childLH (childLL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHL (childLH (childLL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childHL (childLH (childLL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHL (childLH (childLL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childHL (childLH (childLL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHL (childLH (childLL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHH (childLH (childLL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))
            (by
              have h : ((childLL (childHH (childLH (childLL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHH (childLH (childLL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childLH (childHH (childLH (childLL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHH (childLH (childLL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHL (childHH (childLH (childLL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHH (childLH (childLL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)
            (by
              have h : ((childHH (childHH (childLH (childLL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHH (childLH (childLL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))) h)))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHL (childLL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childLL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHL (childLL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHL (childLL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHL (childLL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHH (childLL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHH (childLL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHH (childLL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHH (childLL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001220121 :
    adaptiveCoverCheck 9 (childLH (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childLH (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childLH (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childLH (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childLH (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childLH (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childLH (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childLH (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childLH (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childLH (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childLH (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childLH (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childLH (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childLH (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childLH (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childLH (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childLH (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHL (childLH (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childLH (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHL (childLH (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLH (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHL (childLH (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLH (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHL (childLH (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLH (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHH (childLH (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLH (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHH (childLH (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLH (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHH (childLH (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLH (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHH (childLH (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLH (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001220122 :
    adaptiveCoverCheck 9 (childHL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childHL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childHL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childHL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childHL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childHL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childHL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childHL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childHL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childHL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childHL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childHL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childHL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      have h : ((childHL (childHL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001220123 :
    adaptiveCoverCheck 9 (childHH (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHH (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childHH (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childHH (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childHH (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childHH (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childHH (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHH (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childHH (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHH (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHH (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childHH (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childHH (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childHH (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childHH (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childHH (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHH (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childHH (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHH (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      have h : ((childHL (childHH (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001220130 :
    adaptiveCoverCheck 9 (childLL (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childLL (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childLL (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childLL (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childLL (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childLL (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childLL (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childLL (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childLL (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childLL (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childLL (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childLL (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childLL (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childLL (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childLL (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childLL (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childLL (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHL (childLL (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childLL (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHL (childLL (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLL (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHL (childLL (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLL (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHL (childLL (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLL (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHH (childLL (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLL (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHH (childLL (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLL (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHH (childLL (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLL (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHH (childLL (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLL (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001220131 :
    adaptiveCoverCheck 9 (childLH (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childLH (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childLH (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childLH (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childLH (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childLH (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childLH (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childLH (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childLH (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childLH (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childLH (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childLH (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childLH (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childLH (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childLH (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childLH (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childLH (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHL (childLH (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childLH (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHL (childLH (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLH (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHL (childLH (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLH (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHL (childLH (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLH (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHH (childLH (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLH (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHH (childLH (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLH (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHH (childLH (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLH (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHH (childLH (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLH (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001220132 :
    adaptiveCoverCheck 9 (childHL (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHL (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childHL (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childHL (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childHL (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childHL (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childHL (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHL (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childHL (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHL (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHL (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childHL (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childHL (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childHL (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childHL (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childHL (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHL (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childHL (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHL (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      have h : ((childHL (childHL (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001220133 :
    adaptiveCoverCheck 9 (childHH (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHH (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childHH (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childHH (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childHH (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childHH (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childHH (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHH (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childHH (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHH (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHH (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childHH (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childHH (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childHH (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childHH (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childHH (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHH (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childHH (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHH (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      have h : ((childHL (childHH (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001221002 :
    adaptiveCoverCheck 9 (childHL (childLL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childLL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childLL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childLL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childLL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childLL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childLL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childLL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childLL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childLL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001221003 :
    adaptiveCoverCheck 9 (childHH (childLL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childLL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childLL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childLL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childLL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childLL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childLL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childLL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childLL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childLL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001221012 :
    adaptiveCoverCheck 9 (childHL (childLH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childLH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childLH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childLH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childLH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childLH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childLH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childLH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childLH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childLH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001221013 :
    adaptiveCoverCheck 9 (childHH (childLH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childLH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childLH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childLH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childLH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childLH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childLH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childLH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childLH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childLH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001221020 :
    adaptiveCoverCheck 9 (childLL (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childLL (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childLL (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childLL (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childLL (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childLL (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childLL (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childLL (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childLL (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childLL (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childLL (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childLL (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childLL (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childLL (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childLL (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childLL (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childLL (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHL (childLL (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childLL (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHL (childLL (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLL (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHL (childLL (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLL (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHL (childLL (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLL (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHH (childLL (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLL (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHH (childLL (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLL (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHH (childLL (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLL (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHH (childLL (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLL (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001221021 :
    adaptiveCoverCheck 9 (childLH (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childLH (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childLH (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childLH (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childLH (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childLH (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childLH (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childLH (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childLH (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childLH (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childLH (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childLH (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childLH (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childLH (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childLH (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childLH (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childLH (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHL (childLH (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childLH (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHL (childLH (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLH (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHL (childLH (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLH (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHL (childLH (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLH (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHH (childLH (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLH (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHH (childLH (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLH (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHH (childLH (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLH (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHH (childLH (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLH (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001221022 :
    adaptiveCoverCheck 9 (childHL (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHL (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childHL (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childHL (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childHL (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childHL (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childHL (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHL (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childHL (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHL (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHL (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childHL (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childHL (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childHL (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childHL (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childHL (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHL (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childHL (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHL (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      have h : ((childHL (childHL (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001221023 :
    adaptiveCoverCheck 9 (childHH (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHH (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childHH (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childHH (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childHH (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childHH (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childHH (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHH (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childHH (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHH (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHH (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childHH (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childHH (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childHH (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childHH (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childHH (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHH (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childHH (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHH (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      have h : ((childHL (childHH (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001221030 :
    adaptiveCoverCheck 9 (childLL (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childLL (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childLL (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childLL (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childLL (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childLL (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childLL (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childLL (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childLL (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childLL (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childLL (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childLL (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childLL (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childLL (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childLL (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childLL (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childLL (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHL (childLL (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childLL (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHL (childLL (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLL (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHL (childLL (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLL (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHL (childLL (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLL (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHH (childLL (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLL (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHH (childLL (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLL (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHH (childLL (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLL (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHH (childLL (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLL (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001221031 :
    adaptiveCoverCheck 9 (childLH (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childLH (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childLH (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childLH (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childLH (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childLH (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childLH (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childLH (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childLH (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childLH (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childLH (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childLH (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childLH (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childLH (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childLH (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childLH (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childLH (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHL (childLH (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childLH (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHL (childLH (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLH (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHL (childLH (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLH (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHL (childLH (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLH (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHH (childLH (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLH (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHH (childLH (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLH (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHH (childLH (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLH (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHH (childLH (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLH (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001221032 :
    adaptiveCoverCheck 9 (childHL (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHL (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childHL (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childHL (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childHL (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childHL (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childHL (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHL (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childHL (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHL (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHL (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childHL (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childHL (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childHL (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childHL (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childHL (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHL (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childHL (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHL (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      have h : ((childHL (childHL (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001221033 :
    adaptiveCoverCheck 9 (childHH (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHH (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childHH (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childHH (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childHH (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childHH (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childHH (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHH (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childHH (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHH (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHH (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childHH (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childHH (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childHH (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childHH (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childHH (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHH (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childHH (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHH (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      have h : ((childHL (childHH (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001221102 :
    adaptiveCoverCheck 9 (childHL (childLL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childLL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childLL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childLL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childLL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childLL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childLL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childLL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childLL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childLL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001221103 :
    adaptiveCoverCheck 9 (childHH (childLL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childLL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childLL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childLL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childLL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childLL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childLL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childLL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childLL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childLL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001221112 :
    adaptiveCoverCheck 9 (childHL (childLH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childLH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childLH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childLH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childLH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childLH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childLH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childLH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childLH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childLH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001221113 :
    adaptiveCoverCheck 9 (childHH (childLH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childLH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childLH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childLH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childLH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childLH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childLH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childLH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childLH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childLH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001221120 :
    adaptiveCoverCheck 9 (childLL (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childLL (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childLL (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childLL (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childLL (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childLL (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childLL (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childLL (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childLL (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childLL (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childLL (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childLL (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childLL (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childLL (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childLL (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childLL (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childLL (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHL (childLL (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childLL (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHL (childLL (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLL (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHL (childLL (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLL (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHL (childLL (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLL (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHH (childLL (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLL (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHH (childLL (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLL (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHH (childLL (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLL (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHH (childLL (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLL (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001221121 :
    adaptiveCoverCheck 9 (childLH (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childLH (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childLH (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childLH (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childLH (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childLH (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childLH (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childLH (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childLH (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childLH (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childLH (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childLH (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childLH (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childLH (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childLH (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childLH (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childLH (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHL (childLH (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childLH (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHL (childLH (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLH (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHL (childLH (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLH (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHL (childLH (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLH (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHH (childLH (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLH (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHH (childLH (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLH (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHH (childLH (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLH (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHH (childLH (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLH (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001221122 :
    adaptiveCoverCheck 9 (childHL (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHL (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childHL (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childHL (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childHL (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childHL (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childHL (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHL (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childHL (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHL (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHL (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childHL (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childHL (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childHL (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childHL (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childHL (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHL (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childHL (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHL (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      have h : ((childHL (childHL (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001221123 :
    adaptiveCoverCheck 9 (childHH (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHH (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childHH (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childHH (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childHH (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childHH (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childHH (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHH (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childHH (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHH (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHH (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childHH (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childHH (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childHH (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childHH (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childHH (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHH (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childHH (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHH (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      have h : ((childHL (childHH (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001221130 :
    adaptiveCoverCheck 9 (childLL (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childLL (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childLL (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childLL (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childLL (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childLL (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childLL (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childLL (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childLL (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childLL (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childLL (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childLL (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childLL (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childLL (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childLL (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childLL (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childLL (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHL (childLL (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childLL (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHL (childLL (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLL (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHL (childLL (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLL (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHL (childLL (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLL (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHH (childLL (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLL (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHH (childLL (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLL (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHH (childLL (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLL (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHH (childLL (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLL (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001221131 :
    adaptiveCoverCheck 9 (childLH (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childLH (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childLH (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childLH (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childLH (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childLH (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childLH (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childLH (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childLH (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childLH (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childLH (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childLH (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childLH (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childLH (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childLH (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childLH (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childLH (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHL (childLH (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childLH (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHL (childLH (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLH (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHL (childLH (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLH (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHL (childLH (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLH (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHH (childLH (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLH (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHH (childLH (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLH (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHH (childLH (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLH (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHH (childLH (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLH (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001221132 :
    adaptiveCoverCheck 9 (childHL (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHL (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childHL (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childHL (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childHL (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childHL (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childHL (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHL (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childHL (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHL (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHL (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childHL (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childHL (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childHL (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childHL (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childHL (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHL (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childHL (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHL (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      have h : ((childHL (childHL (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001221133 :
    adaptiveCoverCheck 9 (childHH (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHH (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childHH (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childHH (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childHH (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childHH (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childHH (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHH (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childHH (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHH (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHH (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childHH (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childHH (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childHH (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childHH (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childHH (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHH (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childHH (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHH (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      have h : ((childHL (childHH (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001230002 :
    adaptiveCoverCheck 9 (childHL (childLL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childLL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childLL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childLL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childLL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childLL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childLL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childLL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childLL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childLL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001230003 :
    adaptiveCoverCheck 9 (childHH (childLL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childLL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childLL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childLL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childLL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childLL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childLL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childLL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childLL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childLL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001230012 :
    adaptiveCoverCheck 9 (childHL (childLH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childLH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childLH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childLH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childLH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childLH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childLH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childLH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childLH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childLH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001230013 :
    adaptiveCoverCheck 9 (childHH (childLH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childLH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childLH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childLH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childLH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childLH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childLH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childLH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childLH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childLH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001230020 :
    adaptiveCoverCheck 9 (childLL (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childLL (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childLL (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childLL (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childLL (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childLL (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childLL (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childLL (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childLL (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childLL (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childLL (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childLL (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childLL (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childLL (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childLL (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childLL (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childLL (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHL (childLL (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childLL (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHL (childLL (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLL (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHL (childLL (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLL (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHL (childLL (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLL (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHH (childLL (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLL (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHH (childLL (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLL (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHH (childLL (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLL (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHH (childLL (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLL (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001230021 :
    adaptiveCoverCheck 9 (childLH (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childLH (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childLH (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childLH (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childLH (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childLH (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childLH (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childLH (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childLH (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childLH (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childLH (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childLH (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childLH (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childLH (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childLH (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childLH (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childLH (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHL (childLH (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childLH (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHL (childLH (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLH (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHL (childLH (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLH (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHL (childLH (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLH (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHH (childLH (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLH (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHH (childLH (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLH (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHH (childLH (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLH (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHH (childLH (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLH (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001230022 :
    adaptiveCoverCheck 9 (childHL (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHL (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childHL (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childHL (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childHL (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childHL (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childHL (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHL (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childHL (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHL (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHL (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childHL (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childHL (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childHL (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childHL (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childHL (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHL (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childHL (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHL (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      have h : ((childHL (childHL (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001230023 :
    adaptiveCoverCheck 9 (childHH (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHH (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childHH (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childHH (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childHH (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childHH (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childHH (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHH (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childHH (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHH (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHH (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childHH (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childHH (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childHH (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childHH (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childHH (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHH (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childHH (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHH (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      have h : ((childHL (childHH (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001230030 :
    adaptiveCoverCheck 9 (childLL (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childLL (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childLL (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childLL (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childLL (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childLL (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childLL (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childLL (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childLL (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childLL (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childLL (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childLL (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childLL (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childLL (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childLL (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childLL (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childLL (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHL (childLL (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childLL (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHL (childLL (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLL (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHL (childLL (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLL (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHL (childLL (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLL (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHH (childLL (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLL (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHH (childLL (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLL (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHH (childLL (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLL (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHH (childLL (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLL (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001230031 :
    adaptiveCoverCheck 9 (childLH (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childLH (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childLH (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childLH (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childLH (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childLH (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childLH (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childLH (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childLH (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childLH (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childLH (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childLH (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childLH (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childLH (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childLH (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childLH (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childLH (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHL (childLH (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childLH (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHL (childLH (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLH (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHL (childLH (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLH (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHL (childLH (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLH (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHH (childLH (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLH (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHH (childLH (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLH (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHH (childLH (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLH (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHH (childLH (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLH (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001230032 :
    adaptiveCoverCheck 9 (childHL (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHL (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childHL (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childHL (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childHL (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childHL (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childHL (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHL (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childHL (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHL (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHL (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childHL (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childHL (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childHL (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childHL (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childHL (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHL (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childHL (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHL (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      have h : ((childHL (childHL (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001230033 :
    adaptiveCoverCheck 9 (childHH (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHH (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childHH (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childHH (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childHH (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childHH (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childHH (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHH (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childHH (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHH (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHH (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childHH (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childHH (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childHH (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childHH (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childHH (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHH (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childHH (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHH (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      have h : ((childHL (childHH (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001230102 :
    adaptiveCoverCheck 9 (childHL (childLL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childLL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childLL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childLL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childLL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childLL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childLL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childLL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childLL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childLL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001230103 :
    adaptiveCoverCheck 9 (childHH (childLL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childLL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childLL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childLL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childLL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childLL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childLL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childLL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childLL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childLL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001230112 :
    adaptiveCoverCheck 9 (childHL (childLH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childLH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childLH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childLH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childLH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childLH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childLH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childLH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childLH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childLH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001230113 :
    adaptiveCoverCheck 9 (childHH (childLH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childLH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childLH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childLH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childLH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childLH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childLH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childLH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childLH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childLH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001230120 :
    adaptiveCoverCheck 9 (childLL (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childLL (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childLL (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childLL (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childLL (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childLL (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childLL (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childLL (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childLL (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childLL (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childLL (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childLL (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childLL (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childLL (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childLL (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childLL (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childLL (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHL (childLL (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childLL (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHL (childLL (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLL (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHL (childLL (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLL (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHL (childLL (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLL (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHH (childLL (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLL (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHH (childLL (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLL (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHH (childLL (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLL (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHH (childLL (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLL (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001230121 :
    adaptiveCoverCheck 9 (childLH (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childLH (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childLH (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childLH (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childLH (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childLH (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childLH (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childLH (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childLH (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childLH (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childLH (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childLH (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childLH (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childLH (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childLH (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childLH (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childLH (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHL (childLH (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childLH (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHL (childLH (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLH (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHL (childLH (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLH (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHL (childLH (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLH (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHH (childLH (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLH (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHH (childLH (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLH (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHH (childLH (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLH (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHH (childLH (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLH (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001230122 :
    adaptiveCoverCheck 9 (childHL (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHL (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childHL (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childHL (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childHL (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childHL (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childHL (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHL (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childHL (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHL (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHL (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childHL (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childHL (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childHL (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childHL (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childHL (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHL (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childHL (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHL (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      have h : ((childHL (childHL (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001230123 :
    adaptiveCoverCheck 9 (childHH (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHH (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childHH (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childHH (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childHH (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childHH (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childHH (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHH (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childHH (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHH (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHH (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childHH (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childHH (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childHH (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childHH (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childHH (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHH (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childHH (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHH (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      have h : ((childHL (childHH (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001230130 :
    adaptiveCoverCheck 9 (childLL (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childLL (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childLL (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childLL (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childLL (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childLL (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childLL (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childLL (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childLL (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childLL (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childLL (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childLL (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childLL (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childLL (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childLL (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childLL (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childLL (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHL (childLL (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childLL (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHL (childLL (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLL (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHL (childLL (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLL (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHL (childLL (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLL (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHH (childLL (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLL (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHH (childLL (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLL (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHH (childLL (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLL (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHH (childLL (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLL (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))

end PartE
end GerverSofa
