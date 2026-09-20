import GerverSofa.KernelOnly.PartE.E24KC2ProofHelpers

/-! E24KC6 explicit proof-producing certificate batch. -/
noncomputable section

namespace GerverSofa
namespace PartE

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001230131 :
    adaptiveCoverCheck 9 (childLH (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childLH (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childLH (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childLH (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childLH (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childLH (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childLH (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childLH (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childLH (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childLH (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childLH (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childLH (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childLH (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childLH (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childLH (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childLH (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childLH (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHL (childLH (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childLH (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHL (childLH (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLH (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHL (childLH (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLH (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHL (childLH (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLH (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHH (childLH (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLH (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHH (childLH (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLH (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHH (childLH (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLH (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHH (childLH (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLH (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001230132 :
    adaptiveCoverCheck 9 (childHL (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHL (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childHL (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childHL (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childHL (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childHL (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childHL (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHL (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childHL (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHL (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHL (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childHL (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childHL (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childHL (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childHL (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childHL (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHL (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childHL (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHL (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      have h : ((childHL (childHL (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001230133 :
    adaptiveCoverCheck 9 (childHH (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHH (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childHH (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childHH (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childHH (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childHH (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childHH (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHH (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childHH (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHH (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHH (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childHH (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childHH (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childHH (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childHH (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childHH (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHH (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childHH (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHH (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      have h : ((childHL (childHH (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001231002 :
    adaptiveCoverCheck 9 (childHL (childLL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childLL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childLL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childLL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childLL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childLL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childLL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childLL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childLL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childLL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001231020 :
    adaptiveCoverCheck 9 (childLL (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childLL (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childLL (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childLL (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childLL (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childLL (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childLL (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childLL (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childLL (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childLL (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childLL (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childLL (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childLL (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childLL (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childLL (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childLL (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childLL (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHL (childLL (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childLL (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHL (childLL (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLL (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHL (childLL (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLL (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHL (childLL (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLL (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHH (childLL (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLL (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHH (childLL (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLL (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHH (childLL (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLL (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHH (childLL (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLL (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001231021 :
    adaptiveCoverCheck 9 (childLH (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childLH (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childLH (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childLH (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childLH (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childLH (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childLH (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childLH (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childLH (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childLH (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childLH (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childLH (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childLH (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childLH (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childLH (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childLH (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childLH (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHL (childLH (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childLH (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHL (childLH (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLH (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHL (childLH (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLH (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHL (childLH (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLH (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHH (childLH (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLH (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHH (childLH (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLH (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHH (childLH (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLH (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHH (childLH (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLH (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001231022 :
    adaptiveCoverCheck 9 (childHL (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHL (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childHL (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childHL (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childHL (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childHL (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childHL (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHL (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childHL (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHL (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHL (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childHL (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childHL (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childHL (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childHL (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childHL (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHL (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childHL (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHL (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      have h : ((childHL (childHL (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001231023 :
    adaptiveCoverCheck 9 (childHH (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHH (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childHH (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childHH (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childHH (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childHH (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childHH (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHH (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childHH (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHH (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHH (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childHH (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childHH (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childHH (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childHH (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childHH (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHH (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childHH (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHH (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      have h : ((childHL (childHH (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001231030 :
    adaptiveCoverCheck 9 (childLL (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childLL (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childLL (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childLL (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childLL (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childLL (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childLL (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childLL (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childLL (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childLL (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childLL (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childLL (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childLL (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childLL (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childLL (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childLL (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childLL (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHL (childLL (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childLL (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHL (childLL (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLL (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHL (childLL (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLL (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHL (childLL (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLL (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHH (childLL (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLL (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHH (childLL (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLL (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHH (childLL (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLL (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHH (childLL (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLL (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001231031 :
    adaptiveCoverCheck 9 (childLH (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childLH (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childLH (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childLH (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childLH (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childLH (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childLH (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childLH (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childLH (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childLH (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childLH (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childLH (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childLH (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childLH (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childLH (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childLH (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childLH (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHL (childLH (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childLH (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHL (childLH (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLH (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHL (childLH (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLH (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHL (childLH (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLH (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHH (childLH (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLH (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHH (childLH (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLH (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHH (childLH (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLH (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHH (childLH (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLH (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001231032 :
    adaptiveCoverCheck 9 (childHL (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHL (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childHL (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childHL (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childHL (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childHL (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childHL (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHL (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childHL (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHL (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHL (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childHL (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childHL (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childHL (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childHL (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childHL (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHL (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childHL (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHL (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      have h : ((childHL (childHL (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001231033 :
    adaptiveCoverCheck 9 (childHH (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHH (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childHH (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childHH (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childHH (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childHH (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childHH (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHH (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childHH (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHH (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHH (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childHH (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childHH (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childHH (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childHH (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childHH (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHH (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childHH (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHH (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      have h : ((childHL (childHH (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001231120 :
    adaptiveCoverCheck 9 (childLL (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childLL (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childLL (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childLL (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childLL (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childLL (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childLL (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childLL (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childLL (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childLL (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childLL (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childLL (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childLL (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childLL (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childLL (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childLL (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childLL (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHL (childLL (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childLL (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHL (childLL (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLL (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHL (childLL (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLL (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHL (childLL (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLL (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHH (childLL (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLL (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHH (childLL (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLL (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHH (childLL (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLL (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHH (childLL (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLL (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001231121 :
    adaptiveCoverCheck 9 (childLH (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childLH (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childLH (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childLH (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childLH (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childLH (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childLH (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childLH (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childLH (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childLH (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childLH (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childLH (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childLH (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childLH (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childLH (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childLH (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childLH (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHL (childLH (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childLH (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHL (childLH (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLH (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHL (childLH (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLH (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHL (childLH (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLH (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHH (childLH (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLH (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHH (childLH (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLH (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHH (childLH (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLH (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHH (childLH (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLH (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001231122 :
    adaptiveCoverCheck 9 (childHL (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHL (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childHL (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childHL (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childHL (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childHL (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childHL (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHL (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childHL (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHL (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHL (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childHL (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childHL (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childHL (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childHL (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childHL (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHL (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childHL (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHL (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      have h : ((childHL (childHL (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001231123 :
    adaptiveCoverCheck 9 (childHH (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHH (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childHH (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childHH (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childHH (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childHH (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childHH (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHH (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childHH (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHH (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHH (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childHH (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childHH (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childHH (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childHH (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childHH (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHH (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childHH (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHH (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      have h : ((childHL (childHH (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001231130 :
    adaptiveCoverCheck 9 (childLL (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childLL (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childLL (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childLL (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childLL (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childLL (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childLL (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childLL (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childLL (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childLL (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childLL (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childLL (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childLL (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childLL (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childLL (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childLL (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHL (childLL (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childLL (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHL (childLL (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLL (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHL (childLL (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLL (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHL (childLL (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLL (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHH (childLL (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLL (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHH (childLL (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLL (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHH (childLL (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLL (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHH (childLL (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLL (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001231131 :
    adaptiveCoverCheck 9 (childLH (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childLH (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childLH (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childLH (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childLH (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childLH (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childLH (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childLH (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childLH (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childLH (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childLH (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childLH (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childLH (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childLH (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childLH (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHL (childLH (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childLH (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHL (childLH (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLH (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHL (childLH (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLH (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHL (childLH (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLH (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHH (childLH (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLH (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHH (childLH (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLH (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHH (childLH (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLH (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHH (childLH (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLH (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001231132 :
    adaptiveCoverCheck 9 (childHL (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHL (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childHL (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childHL (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childHL (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childHL (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childHL (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHL (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childHL (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHL (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHL (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childHL (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childHL (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childHL (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childHL (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childHL (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHL (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childHL (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHL (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      have h : ((childHL (childHL (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001231133 :
    adaptiveCoverCheck 9 (childHH (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHH (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childHH (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childHH (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childHH (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childHH (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childHH (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHH (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childHH (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHH (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHH (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childHH (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childHH (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childHH (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childHH (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childHH (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHH (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childHH (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHH (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      have h : ((childHL (childHH (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001320020 :
    adaptiveCoverCheck 9 (childLL (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childLL (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childLL (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childLL (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childLL (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childLL (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childLL (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childLL (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childLL (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childLL (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childLL (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childLL (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childLL (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childLL (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childLL (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childLL (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childLL (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHL (childLL (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childLL (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHL (childLL (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLL (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHL (childLL (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLL (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHL (childLL (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLL (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHH (childLL (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLL (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHH (childLL (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLL (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHH (childLL (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLL (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHH (childLL (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLL (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001320021 :
    adaptiveCoverCheck 9 (childLH (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childLH (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childLH (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childLH (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childLH (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childLH (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childLH (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childLH (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childLH (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childLH (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childLH (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childLH (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childLH (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childLH (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childLH (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHL (childLH (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childLH (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHL (childLH (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLH (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHL (childLH (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLH (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHL (childLH (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLH (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHH (childLH (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLH (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHH (childLH (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLH (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHH (childLH (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLH (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHH (childLH (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLH (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001320022 :
    adaptiveCoverCheck 9 (childHL (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHL (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childHL (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childHL (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childHL (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childHL (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childHL (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHL (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childHL (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHL (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHL (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childHL (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childHL (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childHL (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childHL (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childHL (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHL (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childHL (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHL (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      have h : ((childHL (childHL (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001320023 :
    adaptiveCoverCheck 9 (childHH (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHH (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childHH (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childHH (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childHH (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childHH (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childHH (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHH (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childHH (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHH (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHH (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childHH (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childHH (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childHH (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childHH (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childHH (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHH (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childHH (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHH (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      have h : ((childHL (childHH (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001320030 :
    adaptiveCoverCheck 9 (childLL (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHL (childLL (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childLL (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHL (childLL (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLL (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHL (childLL (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLL (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHL (childLL (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLL (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHH (childLL (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLL (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHH (childLL (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLL (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHH (childLL (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLL (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHH (childLL (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLL (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001320031 :
    adaptiveCoverCheck 9 (childLH (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHL (childLH (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childLH (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHL (childLH (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLH (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHL (childLH (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLH (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHL (childLH (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLH (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHH (childLH (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLH (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHH (childLH (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLH (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHH (childLH (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLH (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHH (childLH (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLH (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001320032 :
    adaptiveCoverCheck 9 (childHL (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHL (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childHL (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childHL (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childHL (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childHL (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childHL (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHL (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childHL (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHL (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHL (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childHL (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childHL (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childHL (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childHL (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childHL (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHL (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childHL (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHL (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      have h : ((childHL (childHL (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001320033 :
    adaptiveCoverCheck 9 (childHH (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHH (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childHH (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childHH (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childHH (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childHH (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childHH (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHH (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childHH (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHH (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHH (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childHH (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childHH (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childHH (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childHH (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childHH (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHH (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childHH (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHH (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      have h : ((childHL (childHH (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001320120 :
    adaptiveCoverCheck 9 (childLL (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHL (childLL (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childLL (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHL (childLL (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLL (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHL (childLL (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLL (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHL (childLL (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLL (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHH (childLL (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLL (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHH (childLL (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLL (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHH (childLL (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLL (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHH (childLL (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLL (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001320121 :
    adaptiveCoverCheck 9 (childLH (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHL (childLH (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childLH (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHL (childLH (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLH (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHL (childLH (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLH (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHL (childLH (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLH (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHH (childLH (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLH (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHH (childLH (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLH (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHH (childLH (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLH (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHH (childLH (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLH (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001320122 :
    adaptiveCoverCheck 9 (childHL (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHL (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childHL (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childHL (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childHL (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childHL (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childHL (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHL (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childHL (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHL (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHL (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childHL (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childHL (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childHL (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childHL (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childHL (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHL (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childHL (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHL (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      have h : ((childHL (childHL (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001320123 :
    adaptiveCoverCheck 9 (childHH (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHH (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childHH (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childHH (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childHH (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childHH (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childHH (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHH (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childHH (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHH (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHH (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childHH (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childHH (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childHH (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childHH (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childHH (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHH (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childHH (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHH (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      have h : ((childHL (childHH (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001320130 :
    adaptiveCoverCheck 9 (childLL (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHL (childLL (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childLL (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHL (childLL (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLL (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHL (childLL (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLL (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHL (childLL (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLL (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHH (childLL (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLL (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHH (childLL (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLL (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHH (childLL (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLL (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHH (childLL (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLL (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001320131 :
    adaptiveCoverCheck 9 (childLH (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHL (childLH (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childLH (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHL (childLH (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLH (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHL (childLH (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLH (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHL (childLH (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLH (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHH (childLH (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLH (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHH (childLH (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLH (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHH (childLH (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLH (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHH (childLH (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLH (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001320132 :
    adaptiveCoverCheck 9 (childHL (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHL (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childHL (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childHL (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childHL (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childHL (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childHL (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHL (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childHL (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHL (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHL (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childHL (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childHL (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childHL (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childHL (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childHL (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHL (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childHL (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHL (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      have h : ((childHL (childHL (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001320133 :
    adaptiveCoverCheck 9 (childHH (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHH (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childHH (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childHH (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childHH (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childHH (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childHH (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHH (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childHH (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHH (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHH (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childHH (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childHH (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childHH (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childHH (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childHH (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHH (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childHH (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHH (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      have h : ((childHL (childHH (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001321020 :
    adaptiveCoverCheck 9 (childLL (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHL (childLL (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childLL (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHL (childLL (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLL (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHL (childLL (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLL (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHL (childLL (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLL (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHH (childLL (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLL (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHH (childLL (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLL (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHH (childLL (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLL (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHH (childLL (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLL (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001321021 :
    adaptiveCoverCheck 9 (childLH (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHL (childLH (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childLH (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHL (childLH (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLH (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHL (childLH (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLH (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHL (childLH (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLH (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHH (childLH (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLH (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHH (childLH (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLH (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHH (childLH (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLH (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHH (childLH (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLH (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001321022 :
    adaptiveCoverCheck 9 (childHL (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHL (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childHL (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childHL (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childHL (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childHL (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childHL (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHL (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childHL (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHL (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHL (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childHL (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childHL (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childHL (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childHL (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childHL (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHL (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childHL (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHL (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      have h : ((childHL (childHL (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001321023 :
    adaptiveCoverCheck 9 (childHH (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHH (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childHH (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childHH (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childHH (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childHH (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childHH (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHH (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childHH (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHH (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHH (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childHH (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childHH (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childHH (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childHH (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childHH (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHH (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childHH (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHH (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      have h : ((childHL (childHH (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001321030 :
    adaptiveCoverCheck 9 (childLL (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHL (childLL (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childLL (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHL (childLL (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLL (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHL (childLL (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLL (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHL (childLL (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLL (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHH (childLL (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLL (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHH (childLL (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLL (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHH (childLL (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLL (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHH (childLL (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLL (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001321031 :
    adaptiveCoverCheck 9 (childLH (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHL (childLH (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childLH (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHL (childLH (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLH (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHL (childLH (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLH (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHL (childLH (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLH (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHH (childLH (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLH (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHH (childLH (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLH (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHH (childLH (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLH (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHH (childLH (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLH (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001321032 :
    adaptiveCoverCheck 9 (childHL (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHL (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childHL (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childHL (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childHL (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childHL (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childHL (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHL (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childHL (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHL (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHL (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childHL (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childHL (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childHL (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childHL (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childHL (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHL (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childHL (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHL (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      have h : ((childHL (childHL (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001321033 :
    adaptiveCoverCheck 9 (childHH (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHH (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childHH (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childHH (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childHH (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childHH (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childHH (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHH (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childHH (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHH (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHH (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childHH (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childHH (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childHH (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childHH (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childHH (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHH (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childHH (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHH (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      have h : ((childHL (childHH (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001321120 :
    adaptiveCoverCheck 9 (childLL (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHL (childLL (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childLL (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHL (childLL (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLL (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHL (childLL (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLL (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHL (childLL (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLL (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHH (childLL (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLL (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHH (childLL (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLL (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHH (childLL (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLL (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHH (childLL (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLL (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001321121 :
    adaptiveCoverCheck 9 (childLH (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHL (childLH (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childLH (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHL (childLH (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLH (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHL (childLH (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLH (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHL (childLH (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLH (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHH (childLH (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLH (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHH (childLH (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLH (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHH (childLH (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLH (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHH (childLH (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLH (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001321122 :
    adaptiveCoverCheck 9 (childHL (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHL (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childHL (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childHL (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childHL (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childHL (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childHL (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHL (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childHL (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHL (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHL (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childHL (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childHL (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childHL (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childHL (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childHL (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHL (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childHL (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHL (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      have h : ((childHL (childHL (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001321123 :
    adaptiveCoverCheck 9 (childHH (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHH (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childHH (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childHH (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childHH (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childHH (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childHH (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHH (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childHH (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHH (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHH (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childHH (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childHH (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childHH (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childHH (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childHH (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHH (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childHH (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHH (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      have h : ((childHL (childHH (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001321130 :
    adaptiveCoverCheck 9 (childLL (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHL (childLL (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childLL (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHL (childLL (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLL (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHL (childLL (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLL (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHL (childLL (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLL (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHH (childLL (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLL (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHH (childLL (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLL (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHH (childLL (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLL (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHH (childLL (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLL (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001321131 :
    adaptiveCoverCheck 9 (childLH (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHL (childLH (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childLH (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHL (childLH (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLH (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHL (childLH (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLH (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHL (childLH (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLH (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHH (childLH (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLH (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHH (childLH (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLH (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHH (childLH (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLH (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHH (childLH (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLH (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001321132 :
    adaptiveCoverCheck 9 (childHL (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHL (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childHL (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childHL (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childHL (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childHL (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childHL (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHL (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childHL (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHL (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHL (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childHL (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childHL (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childHL (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childHL (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childHL (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHL (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childHL (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHL (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      have h : ((childHL (childHL (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001321133 :
    adaptiveCoverCheck 9 (childHH (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHH (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childHH (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childHH (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childHH (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childHH (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childHH (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHH (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childHH (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHH (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHH (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childHH (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childHH (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childHH (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childHH (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childHH (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHH (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childHH (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHH (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      have h : ((childHL (childHH (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001330020 :
    adaptiveCoverCheck 9 (childLL (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHL (childLL (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childLL (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHL (childLL (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLL (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHL (childLL (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLL (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHL (childLL (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLL (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHH (childLL (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLL (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHH (childLL (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLL (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHH (childLL (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLL (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHH (childLL (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLL (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001330021 :
    adaptiveCoverCheck 9 (childLH (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHL (childLH (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childLH (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHL (childLH (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLH (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHL (childLH (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLH (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHL (childLH (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLH (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHH (childLH (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLH (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHH (childLH (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLH (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHH (childLH (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLH (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHH (childLH (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLH (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001330022 :
    adaptiveCoverCheck 9 (childHL (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHL (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childHL (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childHL (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childHL (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childHL (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childHL (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHL (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childHL (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHL (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHL (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childHL (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childHL (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childHL (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childHL (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childHL (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHL (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childHL (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHL (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      have h : ((childHL (childHL (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001330023 :
    adaptiveCoverCheck 9 (childHH (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHH (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childHH (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childHH (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childHH (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childHH (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childHH (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHH (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childHH (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHH (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHH (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childHH (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childHH (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childHH (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childHH (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childHH (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHH (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childHH (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHH (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      have h : ((childHL (childHH (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001330030 :
    adaptiveCoverCheck 9 (childLL (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHL (childLL (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childLL (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHL (childLL (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLL (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHL (childLL (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLL (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHL (childLL (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLL (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHH (childLL (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLL (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHH (childLL (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLL (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHH (childLL (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLL (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHH (childLL (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLL (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001330031 :
    adaptiveCoverCheck 9 (childLH (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHL (childLH (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childLH (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHL (childLH (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLH (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHL (childLH (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLH (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHL (childLH (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLH (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHH (childLH (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLH (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHH (childLH (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLH (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHH (childLH (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLH (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHH (childLH (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLH (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001330032 :
    adaptiveCoverCheck 9 (childHL (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHL (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childHL (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childHL (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childHL (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childHL (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childHL (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHL (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childHL (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHL (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHL (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childHL (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childHL (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childHL (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childHL (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childHL (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHL (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childHL (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHL (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      have h : ((childHL (childHL (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001330033 :
    adaptiveCoverCheck 9 (childHH (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHH (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childHH (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childHH (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childHH (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childHH (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childHH (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHH (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childHH (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHH (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHH (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childHH (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childHH (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childHH (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childHH (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childHH (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHH (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childHH (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHH (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      have h : ((childHL (childHH (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001330120 :
    adaptiveCoverCheck 9 (childLL (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHL (childLL (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childLL (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHL (childLL (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLL (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHL (childLL (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLL (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHL (childLL (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLL (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHH (childLL (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLL (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHH (childLL (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLL (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHH (childLL (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLL (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHH (childLL (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLL (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001330121 :
    adaptiveCoverCheck 9 (childLH (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHL (childLH (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childLH (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHL (childLH (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLH (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHL (childLH (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLH (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHL (childLH (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLH (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHH (childLH (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLH (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHH (childLH (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLH (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHH (childLH (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLH (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHH (childLH (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLH (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001330122 :
    adaptiveCoverCheck 9 (childHL (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHL (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childHL (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childHL (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childHL (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childHL (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childHL (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHL (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childHL (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHL (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHL (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childHL (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childHL (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childHL (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childHL (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childHL (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHL (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childHL (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHL (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childHL (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHL (childHL (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childHL (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHL (childHL (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childHL (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHL (childHL (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childHL (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHL (childHL (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childHL (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childHL (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHH (childHL (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childHL (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHH (childHL (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childHL (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHH (childHL (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childHL (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHH (childHL (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childHL (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001330123 :
    adaptiveCoverCheck 9 (childHH (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHH (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childHH (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childHH (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childHH (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childHH (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childHH (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHH (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childHH (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHH (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHH (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childHH (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childHH (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childHH (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childHH (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childHH (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHH (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childHH (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHH (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childHH (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHL (childHH (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childHH (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHL (childHH (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childHH (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHL (childHH (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childHH (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHL (childHH (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childHH (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childHH (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHH (childHH (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childHH (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHH (childHH (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childHH (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHH (childHH (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childHH (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHH (childHH (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childHH (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001330130 :
    adaptiveCoverCheck 9 (childLL (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHL (childLL (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childLL (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHL (childLL (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLL (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHL (childLL (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLL (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHL (childLL (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLL (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHH (childLL (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLL (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHH (childLL (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLL (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHH (childLL (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLL (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHH (childLL (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLL (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001330131 :
    adaptiveCoverCheck 9 (childLH (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHL (childLH (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childLH (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHL (childLH (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLH (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHL (childLH (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLH (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHL (childLH (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLH (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHH (childLH (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLH (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHH (childLH (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLH (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHH (childLH (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLH (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHH (childLH (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLH (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001330132 :
    adaptiveCoverCheck 9 (childHL (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHL (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childHL (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childHL (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childHL (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childHL (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childHL (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHL (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childHL (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHL (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHL (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childHL (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childHL (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childHL (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childHL (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childHL (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHL (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childHL (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHL (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childHL (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHL (childHL (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childHL (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHL (childHL (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childHL (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHL (childHL (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childHL (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHL (childHL (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childHL (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childHL (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHH (childHL (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childHL (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHH (childHL (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childHL (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHH (childHL (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childHL (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHH (childHL (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childHL (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001330133 :
    adaptiveCoverCheck 9 (childHH (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHH (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childHH (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childHH (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childHH (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childHH (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childHH (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHH (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childHH (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHH (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHH (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childHH (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childHH (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childHH (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childHH (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childHH (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHH (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childHH (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHH (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childHH (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHL (childHH (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childHH (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHL (childHH (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childHH (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHL (childHH (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childHH (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHL (childHH (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childHH (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childHH (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHH (childHH (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childHH (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHH (childHH (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childHH (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHH (childHH (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childHH (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHH (childHH (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childHH (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001331020 :
    adaptiveCoverCheck 9 (childLL (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHL (childLL (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childLL (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHL (childLL (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLL (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHL (childLL (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLL (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHL (childLL (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLL (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHH (childLL (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLL (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHH (childLL (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLL (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHH (childLL (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLL (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHH (childLL (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLL (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001331021 :
    adaptiveCoverCheck 9 (childLH (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHL (childLH (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childLH (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHL (childLH (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLH (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHL (childLH (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLH (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHL (childLH (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLH (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHH (childLH (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLH (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHH (childLH (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLH (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHH (childLH (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLH (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHH (childLH (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLH (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001331022 :
    adaptiveCoverCheck 9 (childHL (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHL (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childHL (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childHL (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childHL (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childHL (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childHL (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHL (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childHL (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHL (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHL (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childHL (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childHL (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childHL (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childHL (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childHL (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHL (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childHL (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHL (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childHL (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHL (childHL (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childHL (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHL (childHL (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childHL (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHL (childHL (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childHL (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHL (childHL (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childHL (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childHL (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHH (childHL (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childHL (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHH (childHL (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childHL (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHH (childHL (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childHL (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHH (childHL (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childHL (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001331023 :
    adaptiveCoverCheck 9 (childHH (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHH (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childHH (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childHH (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childHH (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childHH (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childHH (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHH (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childHH (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHH (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHH (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childHH (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childHH (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childHH (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childHH (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childHH (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHH (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childHH (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHH (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childHH (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHL (childHH (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childHH (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHL (childHH (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childHH (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHL (childHH (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childHH (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHL (childHH (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childHH (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childHH (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHH (childHH (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childHH (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHH (childHH (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childHH (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHH (childHH (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childHH (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHH (childHH (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childHH (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001331030 :
    adaptiveCoverCheck 9 (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHL (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHL (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHL (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHL (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHH (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHH (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHH (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHH (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001331031 :
    adaptiveCoverCheck 9 (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHL (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHL (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHL (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHL (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHH (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHH (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHH (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHH (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001331032 :
    adaptiveCoverCheck 9 (childHL (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHL (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childHL (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childHL (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childHL (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childHL (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childHL (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHL (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childHL (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHL (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHL (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childHL (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childHL (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childHL (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childHL (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childHL (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHL (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childHL (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHL (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childHL (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHL (childHL (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childHL (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHL (childHL (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childHL (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHL (childHL (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childHL (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHL (childHL (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childHL (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childHL (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHH (childHL (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childHL (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHH (childHL (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childHL (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHH (childHL (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childHL (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHH (childHL (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childHL (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001331033 :
    adaptiveCoverCheck 9 (childHH (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHH (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childHH (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childHH (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childHH (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childHH (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childHH (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHH (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childHH (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHH (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHH (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childHH (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childHH (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childHH (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childHH (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childHH (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHH (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childHH (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHH (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childHH (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHL (childHH (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childHH (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHL (childHH (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childHH (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHL (childHH (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childHH (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHL (childHH (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childHH (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childHH (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHH (childHH (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childHH (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHH (childHH (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childHH (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHH (childHH (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childHH (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHH (childHH (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childHH (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001331120 :
    adaptiveCoverCheck 9 (childLL (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHL (childLL (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childLL (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHL (childLL (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLL (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHL (childLL (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLL (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHL (childLL (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLL (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHH (childLL (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLL (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHH (childLL (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLL (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHH (childLL (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLL (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHH (childLL (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLL (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001331121 :
    adaptiveCoverCheck 9 (childLH (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHL (childLH (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childLH (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHL (childLH (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLH (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHL (childLH (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLH (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHL (childLH (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLH (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHH (childLH (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLH (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHH (childLH (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLH (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHH (childLH (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLH (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHH (childLH (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLH (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001331122 :
    adaptiveCoverCheck 9 (childHL (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHL (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childHL (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childHL (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childHL (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childHL (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childHL (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHL (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childHL (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHL (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHL (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childHL (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childHL (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childHL (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childHL (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childHL (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHL (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childHL (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHL (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childHL (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHL (childHL (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childHL (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHL (childHL (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childHL (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHL (childHL (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childHL (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHL (childHL (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childHL (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childHL (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHH (childHL (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childHL (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHH (childHL (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childHL (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHH (childHL (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childHL (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHH (childHL (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childHL (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001331123 :
    adaptiveCoverCheck 9 (childHH (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHH (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childHH (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childHH (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childHH (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childHH (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childHH (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHH (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childHH (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHH (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHH (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childHH (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childHH (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childHH (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childHH (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childHH (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHH (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childHH (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHH (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      have h : ((childHL (childHH (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001331130 :
    adaptiveCoverCheck 9 (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHL (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHL (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHL (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHL (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001331131 :
    adaptiveCoverCheck 9 (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHL (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHL (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHL (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHL (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001331132 :
    adaptiveCoverCheck 9 (childHL (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHL (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childHL (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childHL (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childHL (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childHL (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childHL (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHL (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childHL (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHL (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHL (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childHL (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childHL (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childHL (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childHL (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childHL (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHL (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childHL (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHL (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      have h : ((childHL (childHL (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001331133 :
    adaptiveCoverCheck 9 (childHH (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHH (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childHH (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childHH (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childHH (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childHH (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childHH (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHH (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childHH (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHH (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHH (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childHH (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childHH (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childHH (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childHH (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childHH (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHH (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childHH (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHH (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      have h : ((childHL (childHH (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001331301 :
    adaptiveCoverCheck 9 (childLH (childLL (childHH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLL (childHH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childLL (childHH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLL (childHH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childLL (childHH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLL (childHH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childLL (childHH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLL (childHH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childLL (childHH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLL (childHH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001331310 :
    adaptiveCoverCheck 9 (childLL (childLH (childHH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLH (childHH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childLH (childHH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLH (childHH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childLH (childHH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLH (childHH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childLH (childHH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLH (childHH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childLH (childHH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLH (childHH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0001331311 :
    adaptiveCoverCheck 9 (childLH (childLH (childHH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLH (childHH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childLH (childHH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLH (childHH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childLH (childHH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLH (childHH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childLH (childHH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLH (childHH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childLH (childHH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLH (childHH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010220020 :
    adaptiveCoverCheck 9 (childLL (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHL (childLL (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childLL (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHL (childLL (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLL (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHL (childLL (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLL (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHL (childLL (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLL (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHH (childLL (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLL (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHH (childLL (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLL (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHH (childLL (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLL (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHH (childLL (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLL (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010220021 :
    adaptiveCoverCheck 9 (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010220022 :
    adaptiveCoverCheck 9 (childHL (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHL (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childHL (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childHL (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childHL (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childHL (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childHL (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHL (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childHL (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHL (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHL (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childHL (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childHL (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childHL (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childHL (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childHL (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHL (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childHL (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHL (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      have h : ((childHL (childHL (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010220023 :
    adaptiveCoverCheck 9 (childHH (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHH (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childHH (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childHH (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childHH (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childHH (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childHH (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHH (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childHH (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHH (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHH (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childHH (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childHH (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childHH (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childHH (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childHH (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHH (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childHH (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHH (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      have h : ((childHL (childHH (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010220030 :
    adaptiveCoverCheck 9 (childLL (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHL (childLL (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childLL (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHL (childLL (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLL (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHL (childLL (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLL (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHL (childLL (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLL (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHH (childLL (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLL (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHH (childLL (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLL (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHH (childLL (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLL (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHH (childLL (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLL (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010220031 :
    adaptiveCoverCheck 9 (childLH (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHL (childLH (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childLH (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHL (childLH (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLH (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHL (childLH (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLH (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHL (childLH (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLH (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHH (childLH (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLH (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHH (childLH (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLH (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHH (childLH (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLH (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHH (childLH (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLH (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010220032 :
    adaptiveCoverCheck 9 (childHL (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHL (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childHL (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childHL (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childHL (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childHL (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childHL (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHL (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childHL (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHL (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHL (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childHL (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childHL (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childHL (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childHL (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childHL (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHL (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childHL (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHL (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      have h : ((childHL (childHL (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010220033 :
    adaptiveCoverCheck 9 (childHH (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHH (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childHH (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childHH (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childHH (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childHH (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childHH (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHH (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childHH (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHH (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHH (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLH (childHH (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childHH (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLH (childHH (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childHH (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLH (childHH (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHH (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLH (childHH (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHH (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      have h : ((childHL (childHH (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010220120 :
    adaptiveCoverCheck 9 (childLL (childHL (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childHL (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHL (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childHL (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHL (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHL (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHL (childLL (childHL (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childLL (childHL (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHL (childLL (childHL (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLL (childHL (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHL (childLL (childHL (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLL (childHL (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHL (childLL (childHL (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLL (childHL (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHL (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHH (childLL (childHL (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLL (childHL (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHH (childLL (childHL (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLL (childHL (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHH (childLL (childHL (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLL (childHL (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHH (childLL (childHL (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLL (childHL (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010220121 :
    adaptiveCoverCheck 9 (childLH (childHL (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childHL (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHL (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childHL (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHL (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHL (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHL (childLH (childHL (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childLH (childHL (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHL (childLH (childHL (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLH (childHL (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHL (childLH (childHL (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLH (childHL (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHL (childLH (childHL (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLH (childHL (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHL (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHH (childLH (childHL (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLH (childHL (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHH (childLH (childHL (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLH (childHL (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHH (childLH (childHL (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLH (childHL (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHH (childLH (childHL (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLH (childHL (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010220122 :
    adaptiveCoverCheck 9 (childHL (childHL (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHL (childHL (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childLL (childHL (childHL (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childHL (childHL (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childLL (childHL (childHL (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childHL (childHL (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childLL (childHL (childHL (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHL (childHL (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childLL (childHL (childHL (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHL (childHL (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      have h : ((childLH (childHL (childHL (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childHL (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHL (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010220123 :
    adaptiveCoverCheck 9 (childHH (childHL (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childHL (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childHL (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childHL (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHL (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010220130 :
    adaptiveCoverCheck 9 (childLL (childHH (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childHH (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHH (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childHH (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHH (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHH (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHL (childLL (childHH (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childLL (childHH (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHL (childLL (childHH (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLL (childHH (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHL (childLL (childHH (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLL (childHH (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHL (childLL (childHH (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLL (childHH (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHH (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHH (childLL (childHH (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLL (childHH (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHH (childLL (childHH (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLL (childHH (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHH (childLL (childHH (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLL (childHH (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHH (childLL (childHH (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLL (childHH (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010220131 :
    adaptiveCoverCheck 9 (childLH (childHH (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childHH (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHH (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childHH (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHH (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHH (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHL (childLH (childHH (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childLH (childHH (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHL (childLH (childHH (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLH (childHH (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHL (childLH (childHH (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLH (childHH (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHL (childLH (childHH (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLH (childHH (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHH (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHH (childLH (childHH (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLH (childHH (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHH (childLH (childHH (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLH (childHH (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHH (childLH (childHH (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLH (childHH (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHH (childLH (childHH (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLH (childHH (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010220132 :
    adaptiveCoverCheck 9 (childHL (childHH (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childHH (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childHH (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childHH (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHH (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010220133 :
    adaptiveCoverCheck 9 (childHH (childHH (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childHH (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childHH (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childHH (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHH (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH (childLH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010220200 :
    adaptiveCoverCheck 9 (childLL (childLL (childHL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLL (childHL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childLL (childHL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLL (childHL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childLL (childHL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLL (childHL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childLL (childHL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLL (childHL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childLL (childHL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLL (childHL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010220201 :
    adaptiveCoverCheck 9 (childLH (childLL (childHL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLL (childHL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childLL (childHL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLL (childHL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childLL (childHL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLL (childHL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childLL (childHL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLL (childHL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childLL (childHL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLL (childHL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010220210 :
    adaptiveCoverCheck 9 (childLL (childLH (childHL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLH (childHL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childLH (childHL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLH (childHL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childLH (childHL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLH (childHL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childLH (childHL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLH (childHL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childLH (childHL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLH (childHL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010220211 :
    adaptiveCoverCheck 9 (childLH (childLH (childHL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLH (childHL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childLH (childHL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLH (childHL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childLH (childHL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLH (childHL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childLH (childHL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLH (childHL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childLH (childHL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLH (childHL (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010220300 :
    adaptiveCoverCheck 9 (childLL (childLL (childHH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLL (childHH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childLL (childHH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLL (childHH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childLL (childHH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLL (childHH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childLL (childHH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLL (childHH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childLL (childHH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLL (childHH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010220301 :
    adaptiveCoverCheck 9 (childLH (childLL (childHH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLL (childHH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childLL (childHH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLL (childHH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childLL (childHH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLL (childHH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childLL (childHH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLL (childHH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childLL (childHH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLL (childHH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010220310 :
    adaptiveCoverCheck 9 (childLL (childLH (childHH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLH (childHH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childLH (childHH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLH (childHH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childLH (childHH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLH (childHH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childLH (childHH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLH (childHH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childLH (childHH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLH (childHH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010220311 :
    adaptiveCoverCheck 9 (childLH (childLH (childHH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLH (childHH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childLH (childHH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLH (childHH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childLH (childHH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLH (childHH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childLH (childHH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLH (childHH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childLH (childHH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLH (childHH (childLL (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010221020 :
    adaptiveCoverCheck 9 (childLL (childHL (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childHL (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHL (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childHL (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHL (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHL (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHL (childLL (childHL (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childLL (childHL (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHL (childLL (childHL (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLL (childHL (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHL (childLL (childHL (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLL (childHL (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHL (childLL (childHL (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLL (childHL (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHL (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHH (childLL (childHL (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLL (childHL (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHH (childLL (childHL (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLL (childHL (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHH (childLL (childHL (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLL (childHL (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHH (childLL (childHL (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLL (childHL (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010221021 :
    adaptiveCoverCheck 9 (childLH (childHL (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childHL (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHL (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childHL (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHL (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHL (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHL (childLH (childHL (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childLH (childHL (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHL (childLH (childHL (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLH (childHL (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHL (childLH (childHL (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLH (childHL (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHL (childLH (childHL (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLH (childHL (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHL (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHH (childLH (childHL (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLH (childHL (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHH (childLH (childHL (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLH (childHL (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHH (childLH (childHL (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLH (childHL (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHH (childLH (childHL (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLH (childHL (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010221022 :
    adaptiveCoverCheck 9 (childHL (childHL (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childHL (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childHL (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childHL (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHL (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010221023 :
    adaptiveCoverCheck 9 (childHH (childHL (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childHL (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childHL (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childHL (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHL (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010221030 :
    adaptiveCoverCheck 9 (childLL (childHH (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childHH (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHH (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childHH (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHH (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHH (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHL (childLL (childHH (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childLL (childHH (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHL (childLL (childHH (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLL (childHH (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHL (childLL (childHH (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLL (childHH (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHL (childLL (childHH (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLL (childHH (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHH (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHH (childLL (childHH (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLL (childHH (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHH (childLL (childHH (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLL (childHH (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHH (childLL (childHH (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLL (childHH (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHH (childLL (childHH (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLL (childHH (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010221031 :
    adaptiveCoverCheck 9 (childLH (childHH (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childHH (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHH (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childHH (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHH (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHH (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHL (childLH (childHH (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childLH (childHH (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHL (childLH (childHH (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLH (childHH (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHL (childLH (childHH (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLH (childHH (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHL (childLH (childHH (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLH (childHH (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHH (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))
        (by
          have h : ((childLL (childHH (childLH (childHH (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLH (childHH (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childLH (childHH (childLH (childHH (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLH (childHH (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHL (childHH (childLH (childHH (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLH (childHH (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h)
        (by
          have h : ((childHH (childHH (childLH (childHH (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLH (childHH (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010221032 :
    adaptiveCoverCheck 9 (childHL (childHH (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childHH (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childHH (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childHH (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHH (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010221033 :
    adaptiveCoverCheck 9 (childHH (childHH (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childHH (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childHH (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childHH (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHH (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH (childLL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010221120 :
    adaptiveCoverCheck 9 (childLL (childHL (childLH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL (childLH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childHL (childLH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHL (childLH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childHL (childLH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHL (childLH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childHL (childLH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childHL (childLH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childHL (childLH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childHL (childLH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

end PartE
end GerverSofa
