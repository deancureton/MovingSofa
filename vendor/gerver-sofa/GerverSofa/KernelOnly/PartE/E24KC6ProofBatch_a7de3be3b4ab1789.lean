import GerverSofa.KernelOnly.PartE.E24KC2ProofHelpers

/-! E24KC6 explicit proof-producing certificate batch. -/
noncomputable section

namespace GerverSofa
namespace PartE

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011331022 :
    adaptiveCoverCheck 9 (childHL (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011331023 :
    adaptiveCoverCheck 9 (childHH (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011331032 :
    adaptiveCoverCheck 9 (childHL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011331033 :
    adaptiveCoverCheck 9 (childHH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011331122 :
    adaptiveCoverCheck 9 (childHL (childHL (childLH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL (childLH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childHL (childLH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL (childLH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childHL (childLH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL (childLH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childHL (childLH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL (childLH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHL (childLH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL (childLH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011331123 :
    adaptiveCoverCheck 9 (childHH (childHL (childLH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL (childLH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childHL (childLH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL (childLH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childHL (childLH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL (childLH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childHL (childLH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL (childLH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHL (childLH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL (childLH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011331132 :
    adaptiveCoverCheck 9 (childHL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011331133 :
    adaptiveCoverCheck 9 (childHH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011331200 :
    adaptiveCoverCheck 9 (childLL (childLL (childHL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLL (childHL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childLL (childHL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLL (childHL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childLL (childHL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLL (childHL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childLL (childHL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLL (childHL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childLL (childHL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLL (childHL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011331201 :
    adaptiveCoverCheck 9 (childLH (childLL (childHL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLL (childHL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childLL (childHL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLL (childHL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childLL (childHL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLL (childHL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childLL (childHL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLL (childHL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childLL (childHL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLL (childHL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011331210 :
    adaptiveCoverCheck 9 (childLL (childLH (childHL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLH (childHL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childLH (childHL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLH (childHL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childLH (childHL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLH (childHL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childLH (childHL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLH (childHL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childLH (childHL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLH (childHL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011331211 :
    adaptiveCoverCheck 9 (childLH (childLH (childHL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLH (childHL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childLH (childHL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLH (childHL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childLH (childHL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLH (childHL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childLH (childHL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLH (childHL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childLH (childHL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLH (childHL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011331300 :
    adaptiveCoverCheck 9 (childLL (childLL (childHH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLL (childHH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childLL (childHH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLL (childHH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childLL (childHH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLL (childHH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childLL (childHH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLL (childHH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childLL (childHH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLL (childHH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011331301 :
    adaptiveCoverCheck 9 (childLH (childLL (childHH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLL (childHH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childLL (childHH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLL (childHH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childLL (childHH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLL (childHH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childLL (childHH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLL (childHH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childLL (childHH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLL (childHH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011331310 :
    adaptiveCoverCheck 9 (childLL (childLH (childHH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLH (childHH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childLH (childHH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLH (childHH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childLH (childHH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLH (childHH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childLH (childHH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLH (childHH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childLH (childHH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLH (childHH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011331311 :
    adaptiveCoverCheck 9 (childLH (childLH (childHH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLH (childHH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childLH (childHH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLH (childHH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childLH (childHH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLH (childHH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childLH (childHH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLH (childHH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childLH (childHH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLH (childHH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0100220022 :
    adaptiveCoverCheck 9 (childHL (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0100220023 :
    adaptiveCoverCheck 9 (childHH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0100220032 :
    adaptiveCoverCheck 9 (childHL (childHH (childLL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH (childLL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childHH (childLL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH (childLL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childHH (childLL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH (childLL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childHH (childLL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH (childLL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHH (childLL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH (childLL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0100220033 :
    adaptiveCoverCheck 9 (childHH (childHH (childLL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH (childLL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childHH (childLL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH (childLL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childHH (childLL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH (childLL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childHH (childLL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH (childLL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHH (childLL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH (childLL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0100220122 :
    adaptiveCoverCheck 9 (childHL (childHL (childLH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL (childLH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childHL (childLH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL (childLH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childHL (childLH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL (childLH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childHL (childLH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL (childLH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHL (childLH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL (childLH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0100220123 :
    adaptiveCoverCheck 9 (childHH (childHL (childLH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL (childLH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childHL (childLH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL (childLH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childHL (childLH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL (childLH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childHL (childLH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL (childLH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHL (childLH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL (childLH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0100220132 :
    adaptiveCoverCheck 9 (childHL (childHH (childLH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH (childLH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childHH (childLH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH (childLH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childHH (childLH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH (childLH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childHH (childLH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH (childLH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHH (childLH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH (childLH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0100220133 :
    adaptiveCoverCheck 9 (childHH (childHH (childLH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH (childLH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childHH (childLH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH (childLH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childHH (childLH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH (childLH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childHH (childLH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH (childLH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHH (childLH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH (childLH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0100220200 :
    adaptiveCoverCheck 9 (childLL (childLL (childHL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLL (childHL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childLL (childHL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLL (childHL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childLL (childHL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLL (childHL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childLL (childHL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLL (childHL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childLL (childHL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLL (childHL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0100220201 :
    adaptiveCoverCheck 9 (childLH (childLL (childHL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLL (childHL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childLL (childHL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLL (childHL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childLL (childHL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLL (childHL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childLL (childHL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLL (childHL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childLL (childHL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLL (childHL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0100220210 :
    adaptiveCoverCheck 9 (childLL (childLH (childHL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLH (childHL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childLH (childHL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLH (childHL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childLH (childHL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLH (childHL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childLH (childHL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLH (childHL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childLH (childHL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLH (childHL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0100220211 :
    adaptiveCoverCheck 9 (childLH (childLH (childHL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLH (childHL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childLH (childHL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLH (childHL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childLH (childHL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLH (childHL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childLH (childHL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLH (childHL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childLH (childHL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLH (childHL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0100220212 :
    adaptiveCoverCheck 9 (childHL (childLH (childHL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childLH (childHL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childLH (childHL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childLH (childHL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childLH (childHL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childLH (childHL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childLH (childHL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childLH (childHL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childLH (childHL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childLH (childHL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0100220213 :
    adaptiveCoverCheck 9 (childHH (childLH (childHL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childLH (childHL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childLH (childHL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childLH (childHL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childLH (childHL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childLH (childHL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childLH (childHL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childLH (childHL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childLH (childHL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childLH (childHL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0100220300 :
    adaptiveCoverCheck 9 (childLL (childLL (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLL (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childLL (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLL (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childLL (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLL (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childLL (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLL (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childLL (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLL (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0100220301 :
    adaptiveCoverCheck 9 (childLH (childLL (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLL (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childLL (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLL (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childLL (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLL (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childLL (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLL (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childLL (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLL (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0100220302 :
    adaptiveCoverCheck 9 (childHL (childLL (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childLL (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childLL (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childLL (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childLL (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childLL (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childLL (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childLL (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childLL (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childLL (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0100220303 :
    adaptiveCoverCheck 9 (childHH (childLL (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childLL (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childLL (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childLL (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childLL (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childLL (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childLL (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childLL (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childLL (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childLL (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0100220310 :
    adaptiveCoverCheck 9 (childLL (childLH (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLH (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childLH (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLH (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childLH (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLH (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childLH (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLH (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childLH (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLH (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0100220311 :
    adaptiveCoverCheck 9 (childLH (childLH (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLH (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childLH (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLH (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childLH (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLH (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childLH (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLH (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childLH (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLH (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0100220312 :
    adaptiveCoverCheck 9 (childHL (childLH (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childLH (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childLH (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childLH (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childLH (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childLH (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childLH (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childLH (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childLH (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childLH (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0100220313 :
    adaptiveCoverCheck 9 (childHH (childLH (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childLH (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childLH (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childLH (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childLH (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childLH (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childLH (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childLH (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childLH (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childLH (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0100221022 :
    adaptiveCoverCheck 9 (childHL (childHL (childLL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL (childLL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childHL (childLL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL (childLL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childHL (childLL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL (childLL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childHL (childLL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL (childLL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHL (childLL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL (childLL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0100221023 :
    adaptiveCoverCheck 9 (childHH (childHL (childLL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL (childLL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childHL (childLL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL (childLL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childHL (childLL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL (childLL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childHL (childLL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL (childLL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHL (childLL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL (childLL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0100221032 :
    adaptiveCoverCheck 9 (childHL (childHH (childLL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH (childLL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childHH (childLL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH (childLL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childHH (childLL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH (childLL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childHH (childLL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH (childLL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHH (childLL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH (childLL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0100221033 :
    adaptiveCoverCheck 9 (childHH (childHH (childLL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH (childLL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childHH (childLL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH (childLL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childHH (childLL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH (childLL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childHH (childLL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH (childLL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHH (childLL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH (childLL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0100221122 :
    adaptiveCoverCheck 9 (childHL (childHL (childLH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL (childLH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childHL (childLH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL (childLH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childHL (childLH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL (childLH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childHL (childLH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL (childLH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHL (childLH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL (childLH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0100221123 :
    adaptiveCoverCheck 9 (childHH (childHL (childLH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL (childLH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childHL (childLH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL (childLH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childHL (childLH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL (childLH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childHL (childLH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL (childLH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHL (childLH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL (childLH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0100221132 :
    adaptiveCoverCheck 9 (childHL (childHH (childLH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH (childLH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childHH (childLH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH (childLH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childHH (childLH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH (childLH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childHH (childLH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH (childLH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHH (childLH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH (childLH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0100221133 :
    adaptiveCoverCheck 9 (childHH (childHH (childLH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH (childLH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childHH (childLH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH (childLH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childHH (childLH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH (childLH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childHH (childLH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH (childLH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHH (childLH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH (childLH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0100221200 :
    adaptiveCoverCheck 9 (childLL (childLL (childHL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLL (childHL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childLL (childHL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLL (childHL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childLL (childHL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLL (childHL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childLL (childHL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLL (childHL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childLL (childHL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLL (childHL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0100221201 :
    adaptiveCoverCheck 9 (childLH (childLL (childHL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLL (childHL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childLL (childHL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLL (childHL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childLL (childHL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLL (childHL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childLL (childHL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLL (childHL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childLL (childHL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLL (childHL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0100221202 :
    adaptiveCoverCheck 9 (childHL (childLL (childHL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childLL (childHL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childLL (childHL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childLL (childHL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childLL (childHL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childLL (childHL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childLL (childHL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childLL (childHL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childLL (childHL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childLL (childHL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0100221210 :
    adaptiveCoverCheck 9 (childLL (childLH (childHL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLH (childHL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childLH (childHL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLH (childHL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childLH (childHL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLH (childHL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childLH (childHL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLH (childHL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childLH (childHL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLH (childHL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0100221211 :
    adaptiveCoverCheck 9 (childLH (childLH (childHL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLH (childHL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childLH (childHL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLH (childHL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childLH (childHL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLH (childHL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childLH (childHL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLH (childHL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childLH (childHL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLH (childHL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0100221300 :
    adaptiveCoverCheck 9 (childLL (childLL (childHH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLL (childHH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childLL (childHH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLL (childHH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childLL (childHH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLL (childHH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childLL (childHH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLL (childHH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childLL (childHH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLL (childHH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0100221301 :
    adaptiveCoverCheck 9 (childLH (childLL (childHH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLL (childHH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childLL (childHH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLL (childHH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childLL (childHH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLL (childHH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childLL (childHH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLL (childHH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childLL (childHH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLL (childHH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0100221310 :
    adaptiveCoverCheck 9 (childLL (childLH (childHH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLH (childHH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childLH (childHH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLH (childHH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childLH (childHH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLH (childHH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childLH (childHH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLH (childHH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childLH (childHH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLH (childHH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0100221311 :
    adaptiveCoverCheck 9 (childLH (childLH (childHH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLH (childHH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childLH (childHH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLH (childHH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childLH (childHH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLH (childHH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childLH (childHH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLH (childHH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childLH (childHH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLH (childHH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0100230022 :
    adaptiveCoverCheck 9 (childHL (childHL (childLL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL (childLL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childHL (childLL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL (childLL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childHL (childLL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL (childLL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childHL (childLL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL (childLL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHL (childLL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL (childLL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0100230023 :
    adaptiveCoverCheck 9 (childHH (childHL (childLL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL (childLL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childHL (childLL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL (childLL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childHL (childLL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL (childLL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childHL (childLL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL (childLL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHL (childLL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL (childLL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0100230032 :
    adaptiveCoverCheck 9 (childHL (childHH (childLL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH (childLL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childHH (childLL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH (childLL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childHH (childLL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH (childLL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childHH (childLL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH (childLL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHH (childLL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH (childLL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0100230033 :
    adaptiveCoverCheck 9 (childHH (childHH (childLL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH (childLL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childHH (childLL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH (childLL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childHH (childLL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH (childLL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childHH (childLL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH (childLL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHH (childLL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH (childLL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0100230122 :
    adaptiveCoverCheck 9 (childHL (childHL (childLH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL (childLH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childHL (childLH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL (childLH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childHL (childLH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL (childLH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childHL (childLH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL (childLH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHL (childLH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL (childLH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0100230123 :
    adaptiveCoverCheck 9 (childHH (childHL (childLH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL (childLH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childHL (childLH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL (childLH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childHL (childLH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL (childLH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childHL (childLH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL (childLH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHL (childLH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL (childLH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0100230132 :
    adaptiveCoverCheck 9 (childHL (childHH (childLH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH (childLH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childHH (childLH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH (childLH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childHH (childLH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH (childLH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childHH (childLH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH (childLH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHH (childLH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH (childLH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0100230133 :
    adaptiveCoverCheck 9 (childHH (childHH (childLH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH (childLH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childHH (childLH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH (childLH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childHH (childLH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH (childLH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childHH (childLH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH (childLH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHH (childLH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH (childLH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0100230200 :
    adaptiveCoverCheck 9 (childLL (childLL (childHL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLL (childHL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childLL (childHL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLL (childHL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childLL (childHL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLL (childHL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childLL (childHL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLL (childHL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childLL (childHL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLL (childHL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0100230201 :
    adaptiveCoverCheck 9 (childLH (childLL (childHL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLL (childHL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childLL (childHL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLL (childHL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childLL (childHL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLL (childHL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childLL (childHL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLL (childHL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childLL (childHL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLL (childHL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0100230210 :
    adaptiveCoverCheck 9 (childLL (childLH (childHL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLH (childHL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childLH (childHL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLH (childHL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childLH (childHL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLH (childHL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childLH (childHL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLH (childHL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childLH (childHL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLH (childHL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0100230211 :
    adaptiveCoverCheck 9 (childLH (childLH (childHL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLH (childHL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childLH (childHL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLH (childHL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childLH (childHL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLH (childHL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childLH (childHL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLH (childHL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childLH (childHL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLH (childHL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0100230300 :
    adaptiveCoverCheck 9 (childLL (childLL (childHH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLL (childHH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childLL (childHH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLL (childHH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childLL (childHH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLL (childHH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childLL (childHH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLL (childHH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childLL (childHH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLL (childHH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0100230301 :
    adaptiveCoverCheck 9 (childLH (childLL (childHH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLL (childHH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childLL (childHH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLL (childHH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childLL (childHH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLL (childHH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childLL (childHH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLL (childHH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childLL (childHH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLL (childHH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0100230310 :
    adaptiveCoverCheck 9 (childLL (childLH (childHH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLH (childHH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childLH (childHH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLH (childHH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childLH (childHH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLH (childHH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childLH (childHH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLH (childHH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childLH (childHH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLH (childHH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0100230311 :
    adaptiveCoverCheck 9 (childLH (childLH (childHH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLH (childHH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childLH (childHH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLH (childHH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childLH (childHH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLH (childHH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childLH (childHH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLH (childHH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childLH (childHH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLH (childHH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0100231022 :
    adaptiveCoverCheck 9 (childHL (childHL (childLL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL (childLL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childHL (childLL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL (childLL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childHL (childLL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL (childLL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childHL (childLL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL (childLL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHL (childLL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL (childLL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0100231023 :
    adaptiveCoverCheck 9 (childHH (childHL (childLL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL (childLL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childHL (childLL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL (childLL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childHL (childLL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL (childLL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childHL (childLL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL (childLL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHL (childLL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL (childLL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0100231032 :
    adaptiveCoverCheck 9 (childHL (childHH (childLL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH (childLL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childHH (childLL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH (childLL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childHH (childLL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH (childLL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childHH (childLL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH (childLL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHH (childLL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH (childLL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0100231033 :
    adaptiveCoverCheck 9 (childHH (childHH (childLL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH (childLL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childHH (childLL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH (childLL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childHH (childLL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH (childLL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childHH (childLL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH (childLL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHH (childLL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH (childLL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0100231122 :
    adaptiveCoverCheck 9 (childHL (childHL (childLH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL (childLH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childHL (childLH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL (childLH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childHL (childLH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL (childLH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childHL (childLH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL (childLH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHL (childLH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL (childLH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0100231123 :
    adaptiveCoverCheck 9 (childHH (childHL (childLH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL (childLH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childHL (childLH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL (childLH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childHL (childLH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL (childLH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childHL (childLH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL (childLH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHL (childLH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL (childLH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0100231132 :
    adaptiveCoverCheck 9 (childHL (childHH (childLH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH (childLH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childHH (childLH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH (childLH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childHH (childLH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH (childLH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childHH (childLH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH (childLH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHH (childLH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH (childLH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0100231133 :
    adaptiveCoverCheck 9 (childHH (childHH (childLH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH (childLH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childHH (childLH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH (childLH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childHH (childLH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH (childLH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childHH (childLH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH (childLH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHH (childLH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH (childLH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0100320022 :
    adaptiveCoverCheck 9 (childHL (childHL (childLL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL (childLL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childHL (childLL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL (childLL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childHL (childLL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL (childLL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childHL (childLL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL (childLL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHL (childLL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL (childLL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0100320023 :
    adaptiveCoverCheck 9 (childHH (childHL (childLL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL (childLL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childHL (childLL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL (childLL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childHL (childLL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL (childLL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childHL (childLL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL (childLL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHL (childLL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL (childLL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0100320032 :
    adaptiveCoverCheck 9 (childHL (childHH (childLL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH (childLL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childHH (childLL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH (childLL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childHH (childLL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH (childLL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childHH (childLL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH (childLL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHH (childLL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH (childLL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0100320033 :
    adaptiveCoverCheck 9 (childHH (childHH (childLL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH (childLL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childHH (childLL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH (childLL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childHH (childLL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH (childLL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childHH (childLL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH (childLL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHH (childLL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH (childLL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0100320122 :
    adaptiveCoverCheck 9 (childHL (childHL (childLH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL (childLH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childHL (childLH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL (childLH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childHL (childLH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL (childLH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childHL (childLH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL (childLH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHL (childLH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL (childLH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0100320123 :
    adaptiveCoverCheck 9 (childHH (childHL (childLH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL (childLH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childHL (childLH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL (childLH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childHL (childLH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL (childLH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childHL (childLH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL (childLH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHL (childLH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL (childLH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0100320132 :
    adaptiveCoverCheck 9 (childHL (childHH (childLH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH (childLH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childHH (childLH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH (childLH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childHH (childLH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH (childLH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childHH (childLH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH (childLH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHH (childLH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH (childLH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0100320133 :
    adaptiveCoverCheck 9 (childHH (childHH (childLH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH (childLH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childHH (childLH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH (childLH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childHH (childLH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH (childLH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childHH (childLH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH (childLH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHH (childLH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH (childLH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111030223 :
    adaptiveCoverCheck 9 (childHH (childHL (childHL (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL (childHL (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childHH (childHL (childHL (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL (childHL (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childHH (childHL (childHL (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL (childHL (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHL (childHH (childHL (childHL (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL (childHL (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childHH (childHL (childHL (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL (childHL (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111030232 :
    adaptiveCoverCheck 9 (childHL (childHH (childHL (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH (childHL (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childHL (childHH (childHL (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH (childHL (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childHL (childHH (childHL (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH (childHL (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHL (childHL (childHH (childHL (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH (childHL (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childHL (childHH (childHL (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH (childHL (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111030233 :
    adaptiveCoverCheck 9 (childHH (childHH (childHL (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH (childHL (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childHH (childHH (childHL (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH (childHL (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childHH (childHH (childHL (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH (childHL (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHL (childHH (childHH (childHL (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH (childHL (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childHH (childHH (childHL (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH (childHL (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111030312 :
    adaptiveCoverCheck 9 (childHL (childLH (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childLH (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childHL (childLH (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childLH (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childHL (childLH (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childLH (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHL (childHL (childLH (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childLH (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childHL (childLH (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childLH (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111030313 :
    adaptiveCoverCheck 9 (childHH (childLH (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childLH (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childHH (childLH (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childLH (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childHH (childLH (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childLH (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHL (childHH (childLH (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childLH (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childHH (childLH (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childLH (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111030320 :
    adaptiveCoverCheck 9 (childLL (childHL (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childLL (childHL (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHL (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childLL (childHL (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHL (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHL (childLL (childHL (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childHL (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childLL (childHL (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childHL (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111030321 :
    adaptiveCoverCheck 9 (childLH (childHL (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childLH (childHL (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHL (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childLH (childHL (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHL (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHL (childLH (childHL (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childHL (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childLH (childHL (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childHL (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111030322 :
    adaptiveCoverCheck 9 (childHL (childHL (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childHL (childHL (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childHL (childHL (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHL (childHL (childHL (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childHL (childHL (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111030323 :
    adaptiveCoverCheck 9 (childHH (childHL (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childHH (childHL (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childHH (childHL (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHL (childHH (childHL (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childHH (childHL (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111030330 :
    adaptiveCoverCheck 9 (childLL (childHH (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childLL (childHH (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHH (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childLL (childHH (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHH (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHL (childLL (childHH (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childHH (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childLL (childHH (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childHH (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111030331 :
    adaptiveCoverCheck 9 (childLH (childHH (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childLH (childHH (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHH (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childLH (childHH (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHH (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHL (childLH (childHH (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childHH (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childLH (childHH (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childHH (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111030332 :
    adaptiveCoverCheck 9 (childHL (childHH (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childHL (childHH (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childHL (childHH (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHL (childHL (childHH (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childHL (childHH (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111030333 :
    adaptiveCoverCheck 9 (childHH (childHH (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childHH (childHH (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childHH (childHH (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHL (childHH (childHH (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childHH (childHH (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111031202 :
    adaptiveCoverCheck 9 (childHL (childLL (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childLL (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childHL (childLL (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childLL (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childHL (childLL (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childLL (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHL (childHL (childLL (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childLL (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childHL (childLL (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childLL (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111031220 :
    adaptiveCoverCheck 9 (childLL (childHL (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childLL (childHL (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHL (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childLL (childHL (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHL (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHL (childLL (childHL (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childHL (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childLL (childHL (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childHL (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111031221 :
    adaptiveCoverCheck 9 (childLH (childHL (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childLH (childHL (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHL (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childLH (childHL (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHL (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHL (childLH (childHL (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childHL (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childLH (childHL (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childHL (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111031222 :
    adaptiveCoverCheck 9 (childHL (childHL (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childHL (childHL (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childHL (childHL (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHL (childHL (childHL (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childHL (childHL (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111031223 :
    adaptiveCoverCheck 9 (childHH (childHL (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childHH (childHL (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childHH (childHL (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHL (childHH (childHL (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childHH (childHL (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111031230 :
    adaptiveCoverCheck 9 (childLL (childHH (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childLL (childHH (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHH (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childLL (childHH (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHH (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHL (childLL (childHH (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childHH (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childLL (childHH (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childHH (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111031231 :
    adaptiveCoverCheck 9 (childLH (childHH (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childLH (childHH (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHH (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childLH (childHH (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHH (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHL (childLH (childHH (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childHH (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childLH (childHH (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childHH (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111031232 :
    adaptiveCoverCheck 9 (childHL (childHH (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childHL (childHH (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childHL (childHH (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHL (childHL (childHH (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childHL (childHH (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111031233 :
    adaptiveCoverCheck 9 (childHH (childHH (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childHH (childHH (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childHH (childHH (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHL (childHH (childHH (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childHH (childHH (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111031320 :
    adaptiveCoverCheck 9 (childLL (childHL (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childLL (childHL (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHL (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childLL (childHL (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHL (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHL (childLL (childHL (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childHL (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childLL (childHL (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childHL (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111031321 :
    adaptiveCoverCheck 9 (childLH (childHL (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childLH (childHL (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHL (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childLH (childHL (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHL (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHL (childLH (childHL (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childHL (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childLH (childHL (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childHL (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111031322 :
    adaptiveCoverCheck 9 (childHL (childHL (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childHL (childHL (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childHL (childHL (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHL (childHL (childHL (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childHL (childHL (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111031323 :
    adaptiveCoverCheck 9 (childHH (childHL (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childHH (childHL (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childHH (childHL (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHL (childHH (childHL (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childHH (childHL (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111031330 :
    adaptiveCoverCheck 9 (childLL (childHH (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childLL (childHH (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHH (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childLL (childHH (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHH (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHL (childLL (childHH (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childHH (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childLL (childHH (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childHH (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111031331 :
    adaptiveCoverCheck 9 (childLH (childHH (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childLH (childHH (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHH (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childLH (childHH (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHH (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHL (childLH (childHH (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childHH (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childLH (childHH (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childHH (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111031332 :
    adaptiveCoverCheck 9 (childHL (childHH (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childHL (childHH (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childHL (childHH (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHL (childHL (childHH (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childHL (childHH (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111031333 :
    adaptiveCoverCheck 9 (childHH (childHH (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childHH (childHH (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childHH (childHH (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHL (childHH (childHH (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childHH (childHH (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111032100 :
    adaptiveCoverCheck 9 (childLL (childLL (childLH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLL (childLH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childLL (childLL (childLH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLL (childLH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childLL (childLL (childLH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLL (childLH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHL (childLL (childLL (childLH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLL (childLH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childLL (childLL (childLH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLL (childLH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111032101 :
    adaptiveCoverCheck 9 (childLH (childLL (childLH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLL (childLH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childLH (childLL (childLH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLL (childLH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childLH (childLL (childLH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLL (childLH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHL (childLH (childLL (childLH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLL (childLH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childLH (childLL (childLH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLL (childLH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111032110 :
    adaptiveCoverCheck 9 (childLL (childLH (childLH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLH (childLH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childLL (childLH (childLH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLH (childLH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childLL (childLH (childLH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLH (childLH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHL (childLL (childLH (childLH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLH (childLH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childLL (childLH (childLH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLH (childLH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111032111 :
    adaptiveCoverCheck 9 (childLH (childLH (childLH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLH (childLH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childLH (childLH (childLH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLH (childLH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childLH (childLH (childLH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLH (childLH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHL (childLH (childLH (childLH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLH (childLH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childLH (childLH (childLH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLH (childLH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111033000 :
    adaptiveCoverCheck 9 (childLL (childLL (childLL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLL (childLL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childLL (childLL (childLL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLL (childLL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childLL (childLL (childLL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLL (childLL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHL (childLL (childLL (childLL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLL (childLL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childLL (childLL (childLL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLL (childLL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111033001 :
    adaptiveCoverCheck 9 (childLH (childLL (childLL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLL (childLL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childLH (childLL (childLL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLL (childLL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childLH (childLL (childLL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLL (childLL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHL (childLH (childLL (childLL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLL (childLL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childLH (childLL (childLL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLL (childLL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111033010 :
    adaptiveCoverCheck 9 (childLL (childLH (childLL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLH (childLL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childLL (childLH (childLL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLH (childLL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childLL (childLH (childLL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLH (childLL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHL (childLL (childLH (childLL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLH (childLL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childLL (childLH (childLL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLH (childLL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111033011 :
    adaptiveCoverCheck 9 (childLH (childLH (childLL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLH (childLL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childLH (childLH (childLL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLH (childLL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childLH (childLH (childLL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLH (childLL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHL (childLH (childLH (childLL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLH (childLL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childLH (childLH (childLL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLH (childLL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111033100 :
    adaptiveCoverCheck 9 (childLL (childLL (childLH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLL (childLH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childLL (childLL (childLH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLL (childLH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childLL (childLL (childLH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLL (childLH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHL (childLL (childLL (childLH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLL (childLH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childLL (childLL (childLH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLL (childLH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111033101 :
    adaptiveCoverCheck 9 (childLH (childLL (childLH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLL (childLH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childLH (childLL (childLH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLL (childLH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childLH (childLL (childLH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLL (childLH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHL (childLH (childLL (childLH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLL (childLH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childLH (childLL (childLH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLL (childLH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111033110 :
    adaptiveCoverCheck 9 (childLL (childLH (childLH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLH (childLH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childLL (childLH (childLH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLH (childLH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childLL (childLH (childLH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLH (childLH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHL (childLL (childLH (childLH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLH (childLH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childLL (childLH (childLH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLH (childLH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111033111 :
    adaptiveCoverCheck 9 (childLH (childLH (childLH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLH (childLH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childLH (childLH (childLH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLH (childLH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childLH (childLH (childLH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLH (childLH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHL (childLH (childLH (childLH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLH (childLH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childLH (childLH (childLH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLH (childLH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111120220 :
    adaptiveCoverCheck 9 (childLL (childHL (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childLL (childHL (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHL (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childLL (childHL (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHL (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHL (childLL (childHL (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childHL (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childLL (childHL (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childHL (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111120221 :
    adaptiveCoverCheck 9 (childLH (childHL (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childLH (childHL (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHL (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childLH (childHL (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHL (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHL (childLH (childHL (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childHL (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childLH (childHL (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childHL (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111120222 :
    adaptiveCoverCheck 9 (childHL (childHL (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childHL (childHL (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childHL (childHL (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHL (childHL (childHL (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childHL (childHL (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111120223 :
    adaptiveCoverCheck 9 (childHH (childHL (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childHH (childHL (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childHH (childHL (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHL (childHH (childHL (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childHH (childHL (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111120230 :
    adaptiveCoverCheck 9 (childLL (childHH (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childLL (childHH (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHH (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childLL (childHH (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHH (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHL (childLL (childHH (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childHH (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childLL (childHH (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childHH (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111120231 :
    adaptiveCoverCheck 9 (childLH (childHH (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childLH (childHH (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHH (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childLH (childHH (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHH (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHL (childLH (childHH (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childHH (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childLH (childHH (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childHH (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111120232 :
    adaptiveCoverCheck 9 (childHL (childHH (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childHL (childHH (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childHL (childHH (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHL (childHL (childHH (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childHL (childHH (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111120233 :
    adaptiveCoverCheck 9 (childHH (childHH (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childHH (childHH (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childHH (childHH (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHL (childHH (childHH (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childHH (childHH (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111120320 :
    adaptiveCoverCheck 9 (childLL (childHL (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childLL (childHL (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHL (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childLL (childHL (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHL (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHL (childLL (childHL (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childHL (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childLL (childHL (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childHL (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111120321 :
    adaptiveCoverCheck 9 (childLH (childHL (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childLH (childHL (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHL (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childLH (childHL (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHL (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHL (childLH (childHL (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childHL (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childLH (childHL (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childHL (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111120322 :
    adaptiveCoverCheck 9 (childHL (childHL (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childHL (childHL (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childHL (childHL (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHL (childHL (childHL (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childHL (childHL (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111120323 :
    adaptiveCoverCheck 9 (childHH (childHL (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childHH (childHL (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childHH (childHL (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHL (childHH (childHL (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childHH (childHL (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111120330 :
    adaptiveCoverCheck 9 (childLL (childHH (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childLL (childHH (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHH (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childLL (childHH (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHH (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHL (childLL (childHH (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childHH (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childLL (childHH (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childHH (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111120331 :
    adaptiveCoverCheck 9 (childLH (childHH (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childLH (childHH (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHH (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childLH (childHH (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHH (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHL (childLH (childHH (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childHH (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childLH (childHH (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childHH (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111120332 :
    adaptiveCoverCheck 9 (childHL (childHH (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childHL (childHH (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childHL (childHH (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHL (childHL (childHH (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childHL (childHH (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111120333 :
    adaptiveCoverCheck 9 (childHH (childHH (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childHH (childHH (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childHH (childHH (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHL (childHH (childHH (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childHH (childHH (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111121220 :
    adaptiveCoverCheck 9 (childLL (childHL (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childLL (childHL (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHL (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childLL (childHL (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHL (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHL (childLL (childHL (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childHL (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childLL (childHL (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childHL (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111121221 :
    adaptiveCoverCheck 9 (childLH (childHL (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childLH (childHL (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHL (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childLH (childHL (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHL (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHL (childLH (childHL (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childHL (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childLH (childHL (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childHL (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111121222 :
    adaptiveCoverCheck 9 (childHL (childHL (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childHL (childHL (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childHL (childHL (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childHL (childHL (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childHL (childHL (childHL (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childHL (childHL (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childHL (childHL (childHL (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childHL (childHL (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childHL (childHL (childHL (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childHL (childHL (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childHL (childHL (childHL (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childHL (childHL (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childHL (childHL (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childHH (childHL (childHL (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childHL (childHL (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childHH (childHL (childHL (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childHL (childHL (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childHH (childHL (childHL (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childHL (childHL (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childHH (childHL (childHL (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childHL (childHL (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111121223 :
    adaptiveCoverCheck 9 (childHH (childHL (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHH (childHL (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childLL (childHH (childHL (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childHH (childHL (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childLL (childHH (childHL (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childHH (childHL (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childLL (childHH (childHL (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHH (childHL (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childLL (childHH (childHL (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHH (childHL (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHH (childHL (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childLH (childHH (childHL (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childHH (childHL (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childLH (childHH (childHL (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childHH (childHL (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childLH (childHH (childHL (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHH (childHL (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childLH (childHH (childHL (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHH (childHL (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childHH (childHL (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childHL (childHH (childHL (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childHH (childHL (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childHL (childHH (childHL (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childHH (childHL (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childHL (childHH (childHL (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childHH (childHL (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childHL (childHH (childHL (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childHH (childHL (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childHH (childHL (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childHH (childHH (childHL (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childHH (childHL (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childHH (childHH (childHL (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childHH (childHL (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childHH (childHH (childHL (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childHH (childHL (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childHH (childHH (childHL (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childHH (childHL (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111121230 :
    adaptiveCoverCheck 9 (childLL (childHH (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childLL (childHH (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHH (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childLL (childHH (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHH (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHL (childLL (childHH (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childHH (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childLL (childHH (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childHH (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111121231 :
    adaptiveCoverCheck 9 (childLH (childHH (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childLH (childHH (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHH (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childLH (childHH (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHH (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHL (childLH (childHH (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childHH (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childLH (childHH (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childHH (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111121232 :
    adaptiveCoverCheck 9 (childHL (childHH (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHL (childHH (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childLL (childHL (childHH (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childHL (childHH (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childLL (childHL (childHH (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childHL (childHH (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childLL (childHL (childHH (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHL (childHH (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childLL (childHL (childHH (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHL (childHH (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHL (childHH (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childLH (childHL (childHH (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childHL (childHH (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childLH (childHL (childHH (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childHL (childHH (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childLH (childHL (childHH (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHL (childHH (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childLH (childHL (childHH (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHL (childHH (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childHL (childHH (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childHL (childHL (childHH (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childHL (childHH (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childHL (childHL (childHH (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childHL (childHH (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childHL (childHL (childHH (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childHL (childHH (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childHL (childHL (childHH (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childHL (childHH (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childHL (childHH (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childHH (childHL (childHH (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childHL (childHH (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childHH (childHL (childHH (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childHL (childHH (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childHH (childHL (childHH (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childHL (childHH (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childHH (childHL (childHH (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childHL (childHH (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111121233 :
    adaptiveCoverCheck 9 (childHH (childHH (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childHH (childHH (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childHH (childHH (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childHH (childHH (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childHL (childHH (childHH (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childHH (childHH (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childHL (childHH (childHH (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childHH (childHH (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childHL (childHH (childHH (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childHH (childHH (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childHL (childHH (childHH (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childHH (childHH (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childHH (childHH (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childHH (childHH (childHH (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childHH (childHH (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childHH (childHH (childHH (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childHH (childHH (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childHH (childHH (childHH (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childHH (childHH (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childHH (childHH (childHH (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childHH (childHH (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111121322 :
    adaptiveCoverCheck 9 (childHL (childHL (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childHL (childHL (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childHL (childHL (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childHL (childHL (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childHL (childHL (childHL (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childHL (childHL (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childHL (childHL (childHL (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childHL (childHL (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childHL (childHL (childHL (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childHL (childHL (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childHL (childHL (childHL (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childHL (childHL (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childHL (childHL (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childHH (childHL (childHL (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childHL (childHL (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childHH (childHL (childHL (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childHL (childHL (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childHH (childHL (childHL (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childHL (childHL (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childHH (childHL (childHL (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childHL (childHL (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111121323 :
    adaptiveCoverCheck 9 (childHH (childHL (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childHH (childHL (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childHH (childHL (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childHH (childHL (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childHL (childHH (childHL (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childHH (childHL (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childHL (childHH (childHL (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childHH (childHL (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childHL (childHH (childHL (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childHH (childHL (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childHL (childHH (childHL (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childHH (childHL (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childHH (childHL (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childHH (childHH (childHL (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childHH (childHL (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childHH (childHH (childHL (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childHH (childHL (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childHH (childHH (childHL (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childHH (childHL (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childHH (childHH (childHL (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childHH (childHL (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111121332 :
    adaptiveCoverCheck 9 (childHL (childHH (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childHL (childHH (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childHL (childHH (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childHL (childHH (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childHL (childHL (childHH (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childHL (childHH (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childHL (childHL (childHH (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childHL (childHH (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childHL (childHL (childHH (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childHL (childHH (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childHL (childHL (childHH (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childHL (childHH (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childHL (childHH (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childHH (childHL (childHH (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childHL (childHH (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childHH (childHL (childHH (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childHL (childHH (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childHH (childHL (childHH (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childHL (childHH (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childHH (childHL (childHH (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childHL (childHH (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111121333 :
    adaptiveCoverCheck 9 (childHH (childHH (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childHH (childHH (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childHH (childHH (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childHH (childHH (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childHL (childHH (childHH (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childHH (childHH (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childHL (childHH (childHH (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childHH (childHH (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childHL (childHH (childHH (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childHH (childHH (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childHL (childHH (childHH (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childHH (childHH (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childHH (childHH (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childHH (childHH (childHH (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childHH (childHH (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childHH (childHH (childHH (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childHH (childHH (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childHH (childHH (childHH (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childHH (childHH (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childHH (childHH (childHH (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childHH (childHH (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111122000 :
    adaptiveCoverCheck 9 (childLL (childLL (childLL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLL (childLL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childLL (childLL (childLL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLL (childLL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childLL (childLL (childLL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLL (childLL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHL (childLL (childLL (childLL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLL (childLL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childLL (childLL (childLL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLL (childLL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111122001 :
    adaptiveCoverCheck 9 (childLH (childLL (childLL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLL (childLL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childLH (childLL (childLL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLL (childLL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childLH (childLL (childLL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLL (childLL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHL (childLH (childLL (childLL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLL (childLL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childLH (childLL (childLL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLL (childLL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111122010 :
    adaptiveCoverCheck 9 (childLL (childLH (childLL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLH (childLL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childLL (childLH (childLL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLH (childLL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childLL (childLH (childLL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLH (childLL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHL (childLL (childLH (childLL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLH (childLL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childLL (childLH (childLL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLH (childLL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111122011 :
    adaptiveCoverCheck 9 (childLH (childLH (childLL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLH (childLL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childLH (childLH (childLL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLH (childLL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childLH (childLH (childLL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLH (childLL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHL (childLH (childLH (childLL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLH (childLL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childLH (childLH (childLL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLH (childLL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111122100 :
    adaptiveCoverCheck 9 (childLL (childLL (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLL (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childLL (childLL (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLL (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childLL (childLL (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLL (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHL (childLL (childLL (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLL (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childLL (childLL (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLL (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111122101 :
    adaptiveCoverCheck 9 (childLH (childLL (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLL (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childLH (childLL (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLL (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childLH (childLL (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLL (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHL (childLH (childLL (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLL (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childLH (childLL (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLL (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111122110 :
    adaptiveCoverCheck 9 (childLL (childLH (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLH (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childLL (childLH (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLH (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childLH (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childLH (childLL (childLH (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childLL (childLH (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childLH (childLL (childLH (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childLL (childLH (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childLH (childLL (childLH (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childLL (childLH (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childLH (childLL (childLH (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childLL (childLH (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))
    (by
      have h : ((childHL (childLL (childLH (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLH (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childLL (childLH (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLH (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111122111 :
    adaptiveCoverCheck 9 (childLH (childLH (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLH (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childLH (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childLL (childLH (childLH (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childLH (childLH (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childLL (childLH (childLH (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childLH (childLH (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childLL (childLH (childLH (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childLH (childLH (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childLL (childLH (childLH (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childLH (childLH (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childLH (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childLH (childLH (childLH (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childLH (childLH (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childLH (childLH (childLH (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childLH (childLH (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childLH (childLH (childLH (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childLH (childLH (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childLH (childLH (childLH (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childLH (childLH (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))
    (by
      have h : ((childHL (childLH (childLH (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLH (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childLH (childLH (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLH (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111122113 :
    adaptiveCoverCheck 9 (childHH (childLH (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childLH (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childHH (childLH (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childLH (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childHH (childLH (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childLH (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHL (childHH (childLH (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childLH (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childHH (childLH (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childLH (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111123000 :
    adaptiveCoverCheck 9 (childLL (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childLL (childLL (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childLL (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childLL (childLL (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childLL (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childLL (childLL (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childLL (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childLL (childLL (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childLL (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childLH (childLL (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childLL (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childLH (childLL (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childLL (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childLH (childLL (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childLL (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childLH (childLL (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childLL (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))
    (by
      have h : ((childHL (childLL (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childHH (childLL (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLL (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childHH (childLL (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLL (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childHH (childLL (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLL (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childHH (childLL (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLL (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111123001 :
    adaptiveCoverCheck 9 (childLH (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childLL (childLH (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childLH (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childLL (childLH (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childLH (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childLL (childLH (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childLH (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childLL (childLH (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childLH (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childLH (childLH (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childLH (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childLH (childLH (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childLH (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childLH (childLH (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childLH (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childLH (childLH (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childLH (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childHL (childLH (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childLH (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childHL (childLH (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLH (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childHL (childLH (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLH (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childHL (childLH (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLH (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childHH (childLH (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLH (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childHH (childLH (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLH (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childHH (childLH (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLH (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childHH (childLH (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLH (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111123002 :
    adaptiveCoverCheck 9 (childHL (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childHL (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childHL (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHL (childHL (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childHL (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111123003 :
    adaptiveCoverCheck 9 (childHH (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childHH (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childHH (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHL (childHH (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childHH (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111123010 :
    adaptiveCoverCheck 9 (childLL (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childLL (childLL (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childLL (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childLL (childLL (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childLL (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childLL (childLL (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childLL (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childLL (childLL (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childLL (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childLH (childLL (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childLL (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childLH (childLL (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childLL (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childLH (childLL (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childLL (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childLH (childLL (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childLL (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childHL (childLL (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childLL (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childHL (childLL (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLL (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childHL (childLL (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLL (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childHL (childLL (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLL (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childHH (childLL (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLL (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childHH (childLL (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLL (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childHH (childLL (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLL (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childHH (childLL (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLL (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111123011 :
    adaptiveCoverCheck 9 (childLH (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childLL (childLH (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childLH (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childLL (childLH (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childLH (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childLL (childLH (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childLH (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childLL (childLH (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childLH (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childLH (childLH (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childLH (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childLH (childLH (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childLH (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childLH (childLH (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childLH (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childLH (childLH (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childLH (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childHL (childLH (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childLH (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childHL (childLH (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLH (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childHL (childLH (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLH (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childHL (childLH (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLH (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childHH (childLH (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLH (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childHH (childLH (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLH (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childHH (childLH (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLH (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childHH (childLH (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLH (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111123012 :
    adaptiveCoverCheck 9 (childHL (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childHL (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childHL (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHL (childHL (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childHL (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111123013 :
    adaptiveCoverCheck 9 (childHH (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childHH (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childHH (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHL (childHH (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childHH (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111123100 :
    adaptiveCoverCheck 9 (childLL (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childLL (childLL (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childLL (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childLL (childLL (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childLL (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childLL (childLL (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childLL (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childLL (childLL (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childLL (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childLH (childLL (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childLL (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childLH (childLL (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childLL (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childLH (childLL (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childLL (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childLH (childLL (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childLL (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childHL (childLL (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childLL (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childHL (childLL (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLL (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childHL (childLL (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLL (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childHL (childLL (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLL (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childHH (childLL (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLL (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childHH (childLL (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLL (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childHH (childLL (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLL (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childHH (childLL (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLL (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111123101 :
    adaptiveCoverCheck 9 (childLH (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childLL (childLH (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childLH (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childLL (childLH (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childLH (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childLL (childLH (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childLH (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childLL (childLH (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childLH (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childLH (childLH (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childLH (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childLH (childLH (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childLH (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childLH (childLH (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childLH (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childLH (childLH (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childLH (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childHL (childLH (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childLH (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childHL (childLH (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLH (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childHL (childLH (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLH (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childHL (childLH (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLH (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childHH (childLH (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLH (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childHH (childLH (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLH (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childHH (childLH (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLH (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childHH (childLH (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLH (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111123102 :
    adaptiveCoverCheck 9 (childHL (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childHL (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childHL (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHL (childHL (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childHL (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111123103 :
    adaptiveCoverCheck 9 (childHH (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childHH (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childHH (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHL (childHH (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childHH (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111123110 :
    adaptiveCoverCheck 9 (childLL (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childLL (childLL (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childLL (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childLL (childLL (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childLL (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childLL (childLL (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childLL (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childLL (childLL (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childLL (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childLH (childLL (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childLL (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childLH (childLL (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childLL (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childLH (childLL (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childLL (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childLH (childLL (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childLL (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childHL (childLL (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childLL (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childHL (childLL (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLL (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childHL (childLL (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLL (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childHL (childLL (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLL (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childHH (childLL (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLL (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childHH (childLL (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLL (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childHH (childLL (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLL (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childHH (childLL (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLL (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111123111 :
    adaptiveCoverCheck 9 (childLH (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childLL (childLH (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childLH (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childLL (childLH (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childLH (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childLL (childLH (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childLH (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childLL (childLH (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childLH (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childLH (childLH (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childLH (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childLH (childLH (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childLH (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childLH (childLH (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childLH (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childLH (childLH (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childLH (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childHL (childLH (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childLH (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childHL (childLH (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLH (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childHL (childLH (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLH (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childHL (childLH (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLH (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childHH (childLH (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLH (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childHH (childLH (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLH (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childHH (childLH (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLH (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childHH (childLH (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLH (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111123112 :
    adaptiveCoverCheck 9 (childHL (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childHL (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childHL (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHL (childHL (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childHL (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111123113 :
    adaptiveCoverCheck 9 (childHH (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childHH (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childHH (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHL (childHH (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childHH (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111130222 :
    adaptiveCoverCheck 9 (childHL (childHL (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childHL (childHL (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childHL (childHL (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childHL (childHL (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childHL (childHL (childHL (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childHL (childHL (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childHL (childHL (childHL (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childHL (childHL (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childHL (childHL (childHL (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childHL (childHL (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childHL (childHL (childHL (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childHL (childHL (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childHL (childHL (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childHH (childHL (childHL (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childHL (childHL (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childHH (childHL (childHL (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childHL (childHL (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childHH (childHL (childHL (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childHL (childHL (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childHH (childHL (childHL (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childHL (childHL (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111130223 :
    adaptiveCoverCheck 9 (childHH (childHL (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childHH (childHL (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childHH (childHL (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childHH (childHL (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childHL (childHH (childHL (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childHH (childHL (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childHL (childHH (childHL (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childHH (childHL (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childHL (childHH (childHL (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childHH (childHL (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childHL (childHH (childHL (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childHH (childHL (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childHH (childHL (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childHH (childHH (childHL (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childHH (childHL (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childHH (childHH (childHL (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childHH (childHL (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childHH (childHH (childHL (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childHH (childHL (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childHH (childHH (childHL (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childHH (childHL (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111130232 :
    adaptiveCoverCheck 9 (childHL (childHH (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childHL (childHH (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childHL (childHH (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childHL (childHH (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childHL (childHL (childHH (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childHL (childHH (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childHL (childHL (childHH (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childHL (childHH (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childHL (childHL (childHH (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childHL (childHH (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childHL (childHL (childHH (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childHL (childHH (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childHL (childHH (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childHH (childHL (childHH (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childHL (childHH (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childHH (childHL (childHH (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childHL (childHH (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childHH (childHL (childHH (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childHL (childHH (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childHH (childHL (childHH (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childHL (childHH (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111130233 :
    adaptiveCoverCheck 9 (childHH (childHH (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childHH (childHH (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childHH (childHH (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childHH (childHH (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childHL (childHH (childHH (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childHH (childHH (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childHL (childHH (childHH (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childHH (childHH (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childHL (childHH (childHH (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childHH (childHH (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childHL (childHH (childHH (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childHH (childHH (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childHH (childHH (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childHH (childHH (childHH (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childHH (childHH (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childHH (childHH (childHH (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childHH (childHH (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childHH (childHH (childHH (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childHH (childHH (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childHH (childHH (childHH (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childHH (childHH (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111130322 :
    adaptiveCoverCheck 9 (childHL (childHL (childHH (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL (childHH (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childHL (childHL (childHH (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL (childHH (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childHL (childHL (childHH (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL (childHH (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childHL (childHL (childHH (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childHL (childHL (childHL (childHH (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childHL (childHL (childHH (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childHL (childHL (childHL (childHH (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childHL (childHL (childHH (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childHL (childHL (childHL (childHH (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childHL (childHL (childHH (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childHL (childHL (childHL (childHH (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childHL (childHL (childHH (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childHL (childHL (childHH (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childHH (childHL (childHL (childHH (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childHL (childHL (childHH (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childHH (childHL (childHL (childHH (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childHL (childHL (childHH (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childHH (childHL (childHL (childHH (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childHL (childHL (childHH (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childHH (childHL (childHL (childHH (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childHL (childHL (childHH (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111130323 :
    adaptiveCoverCheck 9 (childHH (childHL (childHH (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL (childHH (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childHH (childHL (childHH (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL (childHH (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childHH (childHL (childHH (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL (childHH (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHL (childHH (childHL (childHH (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL (childHH (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childHH (childHL (childHH (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL (childHH (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111130332 :
    adaptiveCoverCheck 9 (childHL (childHH (childHH (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH (childHH (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childHL (childHH (childHH (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH (childHH (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childHL (childHH (childHH (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH (childHH (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHL (childHL (childHH (childHH (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH (childHH (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childHL (childHH (childHH (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH (childHH (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111130333 :
    adaptiveCoverCheck 9 (childHH (childHH (childHH (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH (childHH (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childHH (childHH (childHH (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH (childHH (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childHH (childHH (childHH (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH (childHH (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHL (childHH (childHH (childHH (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH (childHH (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childHH (childHH (childHH (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH (childHH (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111131222 :
    adaptiveCoverCheck 9 (childHL (childHL (childHL (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL (childHL (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childHL (childHL (childHL (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL (childHL (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childHL (childHL (childHL (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL (childHL (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHL (childHL (childHL (childHL (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL (childHL (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childHL (childHL (childHL (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL (childHL (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111131223 :
    adaptiveCoverCheck 9 (childHH (childHL (childHL (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL (childHL (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childHH (childHL (childHL (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL (childHL (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childHH (childHL (childHL (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL (childHL (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHL (childHH (childHL (childHL (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL (childHL (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childHH (childHL (childHL (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL (childHL (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111131232 :
    adaptiveCoverCheck 9 (childHL (childHH (childHL (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH (childHL (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childHL (childHH (childHL (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH (childHL (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childHL (childHH (childHL (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH (childHL (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHL (childHL (childHH (childHL (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH (childHL (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childHL (childHH (childHL (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH (childHL (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111131233 :
    adaptiveCoverCheck 9 (childHH (childHH (childHL (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH (childHL (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childHH (childHH (childHL (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH (childHL (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childHH (childHH (childHL (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH (childHL (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHL (childHH (childHH (childHL (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH (childHL (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childHH (childHH (childHL (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH (childHL (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111131322 :
    adaptiveCoverCheck 9 (childHL (childHL (childHH (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL (childHH (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childHL (childHL (childHH (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL (childHH (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childHL (childHL (childHH (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL (childHH (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHL (childHL (childHL (childHH (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL (childHH (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childHL (childHL (childHH (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL (childHH (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111131323 :
    adaptiveCoverCheck 9 (childHH (childHL (childHH (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL (childHH (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childHH (childHL (childHH (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL (childHH (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childHH (childHL (childHH (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL (childHH (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHL (childHH (childHL (childHH (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL (childHH (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childHH (childHL (childHH (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL (childHH (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111131332 :
    adaptiveCoverCheck 9 (childHL (childHH (childHH (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH (childHH (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childHL (childHH (childHH (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH (childHH (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childHL (childHH (childHH (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH (childHH (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHL (childHL (childHH (childHH (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH (childHH (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childHL (childHH (childHH (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH (childHH (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111131333 :
    adaptiveCoverCheck 9 (childHH (childHH (childHH (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH (childHH (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childHH (childHH (childHH (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH (childHH (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childHH (childHH (childHH (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH (childHH (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHL (childHH (childHH (childHH (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH (childHH (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childHH (childHH (childHH (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH (childHH (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111132000 :
    adaptiveCoverCheck 9 (childLL (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childLL (childLL (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childLL (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childLL (childLL (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childLL (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childLL (childLL (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childLL (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childLL (childLL (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childLL (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childLH (childLL (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childLL (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childLH (childLL (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childLL (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childLH (childLL (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childLL (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childLH (childLL (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childLL (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childHL (childLL (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childLL (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childHL (childLL (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLL (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childHL (childLL (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLL (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childHL (childLL (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLL (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childHH (childLL (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLL (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childHH (childLL (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLL (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childHH (childLL (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLL (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childHH (childLL (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLL (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111132001 :
    adaptiveCoverCheck 9 (childLH (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childLL (childLH (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childLH (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childLL (childLH (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childLH (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childLL (childLH (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childLH (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childLL (childLH (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childLH (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childLH (childLH (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childLH (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childLH (childLH (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childLH (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childLH (childLH (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childLH (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childLH (childLH (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childLH (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childHL (childLH (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childLH (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childHL (childLH (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLH (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childHL (childLH (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLH (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childHL (childLH (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLH (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childHH (childLH (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLH (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childHH (childLH (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLH (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childHH (childLH (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLH (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childHH (childLH (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLH (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111132002 :
    adaptiveCoverCheck 9 (childHL (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childHL (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childHL (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHL (childHL (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childHL (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111132003 :
    adaptiveCoverCheck 9 (childHH (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childHH (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childHH (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHL (childHH (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childHH (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111132010 :
    adaptiveCoverCheck 9 (childLL (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childLL (childLL (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childLL (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childLL (childLL (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childLL (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childLL (childLL (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childLL (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childLL (childLL (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childLL (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childLH (childLL (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childLL (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childLH (childLL (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childLL (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childLH (childLL (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childLL (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childLH (childLL (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childLL (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childHL (childLL (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childLL (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childHL (childLL (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLL (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childHL (childLL (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLL (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childHL (childLL (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLL (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childHH (childLL (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLL (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLH (childHH (childLL (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childLH (childHH (childLL (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childLH (childHH (childLL (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childLH (childHH (childLL (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childLH (childHH (childLL (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childLH (childHH (childLL (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childLH (childHH (childLL (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childLH (childHH (childLL (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childLH (childHH (childLL (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h))
        (by
          have h : ((childHL (childHH (childLL (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLL (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childHH (childLL (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLL (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111132011 :
    adaptiveCoverCheck 9 (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childLL (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childLL (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childLL (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childLL (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childLH (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childLH (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHL (childLH (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childHL (childLH (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHL (childLH (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childHL (childLH (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHL (childLH (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childHL (childLH (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHL (childLH (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childHL (childLH (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHL (childLH (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHH (childLH (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childHH (childLH (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHH (childLH (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childHH (childLH (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHH (childLH (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childHH (childLH (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHH (childLH (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childHH (childLH (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHH (childLH (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLL (childHL (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childLL (childHL (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childLL (childHL (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childLL (childHL (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childLL (childHL (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childLL (childHL (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childLL (childHL (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childLL (childHL (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childLL (childHL (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLH (childHL (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childLH (childHL (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childLH (childHL (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childLH (childHL (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childLH (childHL (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childLH (childHL (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childLH (childHL (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childLH (childHL (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childLH (childHL (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h))
        (by
          have h : ((childHL (childHL (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childHL (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLL (childHH (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childLL (childHH (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childLL (childHH (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childLL (childHH (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childLL (childHH (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childLL (childHH (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childLL (childHH (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childLL (childHH (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childLL (childHH (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLH (childHH (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childLH (childHH (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childLH (childHH (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childLH (childHH (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childLH (childHH (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childLH (childHH (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childLH (childHH (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childLH (childHH (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childLH (childHH (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHL (childHH (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childHL (childHH (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHL (childHH (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childHL (childHH (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHL (childHH (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childHL (childHH (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHL (childHH (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childHL (childHH (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHL (childHH (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHH (childHH (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childHH (childHH (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHH (childHH (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childHH (childHH (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHH (childHH (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childHH (childHH (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHH (childHH (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childHH (childHH (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHH (childHH (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111132012 :
    adaptiveCoverCheck 9 (childHL (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      have h : ((childLL (childHL (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childLH (childHL (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHL (childHL (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childHL (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111132013 :
    adaptiveCoverCheck 9 (childHH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childLL (childHH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childHH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childLL (childHH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childHH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childLL (childHH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childLL (childHH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          have h : ((childLL (childLH (childHH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childHH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childLH (childLH (childHH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childHH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHL (childLH (childHH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          have h : ((childHH (childLH (childHH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h))
    (by
      have h : ((childHL (childHH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)
    (by
      have h : ((childHH (childHH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaBelowLeaf111132100 :
    adaptiveCoverCheck 9 (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLL (childLL (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childLL (childLL (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childLL (childLL (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childLL (childLL (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childLL (childLL (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childLL (childLL (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childLL (childLL (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childLL (childLL (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childLL (childLL (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLH (childLL (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childLH (childLL (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childLH (childLL (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childLH (childLL (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childLH (childLL (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childLH (childLL (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childLH (childLL (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childLH (childLL (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childLH (childLL (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHL (childLL (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childHL (childLL (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHL (childLL (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childHL (childLL (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHL (childLL (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childHL (childLL (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHL (childLL (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childHL (childLL (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHL (childLL (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHH (childLL (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childHH (childLL (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHH (childLL (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childHH (childLL (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHH (childLL (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childHH (childLL (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHH (childLL (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childHH (childLL (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHH (childLL (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLL (childLH (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childLL (childLH (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childLL (childLH (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childLL (childLH (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childLL (childLH (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childLL (childLH (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childLL (childLH (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childLL (childLH (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childLL (childLH (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h))
        (by
          have h : ((childLH (childLH (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))) h)
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHL (childLH (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childHL (childLH (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHL (childLH (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childHL (childLH (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHL (childLH (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childHL (childLH (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHL (childLH (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childHL (childLH (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHL (childLH (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHH (childLH (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childHH (childLH (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHH (childLH (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childHH (childLH (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHH (childLH (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childHH (childLH (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHH (childLH (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childHH (childLH (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHH (childLH (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLL (childHL (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childLL (childHL (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childLL (childHL (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childLL (childHL (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childLL (childHL (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childLL (childHL (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childLL (childHL (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childLL (childHL (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childLL (childHL (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLH (childHL (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childLH (childHL (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childLH (childHL (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childLH (childHL (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childLH (childHL (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childLH (childHL (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childLH (childHL (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childLH (childHL (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childLH (childHL (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHL (childHL (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childHL (childHL (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHL (childHL (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childHL (childHL (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHL (childHL (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childHL (childHL (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHL (childHL (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childHL (childHL (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHL (childHL (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHH (childHL (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childHH (childHL (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHH (childHL (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childHH (childHL (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHH (childHL (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childHH (childHL (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHH (childHL (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childHH (childHL (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHH (childHL (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLL (childHH (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childLL (childHH (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childLL (childHH (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childLL (childHH (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childLL (childHH (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childLL (childHH (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childLL (childHH (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childLL (childHH (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childLL (childHH (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLH (childHH (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childLH (childHH (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childLH (childHH (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childLH (childHH (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childLH (childHH (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childLH (childHH (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childLH (childHH (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childLH (childHH (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childLH (childHH (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHL (childHH (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childHL (childHH (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHL (childHH (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childHL (childHH (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHL (childHH (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childHL (childHH (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHL (childHH (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childHL (childHH (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHL (childHH (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childHH (childHH (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))
            (by
              have h : ((childLL (childHH (childHH (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL (childHH (childHH (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childLH (childHH (childHH (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH (childHH (childHH (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHL (childHH (childHH (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL (childHH (childHH (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)
            (by
              have h : ((childHH (childHH (childHH (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))))))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH (childHH (childHH (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))))) h)))

end PartE
end GerverSofa
