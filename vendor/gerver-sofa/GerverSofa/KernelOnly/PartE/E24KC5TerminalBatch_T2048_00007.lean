import GerverSofa.KernelOnly.PartE.E24KC2ProofHelpers

/-! E24KC5 checkpoint-aware kernel batch. -/
noncomputable section

namespace GerverSofa
namespace PartE

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100330300 :
    adaptiveCoverCheck 9 (childLL (childLL (childHH (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHH (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHH (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100330301 :
    adaptiveCoverCheck 9 (childLH (childLL (childHH (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHH (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHH (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100330302 :
    adaptiveCoverCheck 9 (childHL (childLL (childHH (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHH (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHH (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100330303 :
    adaptiveCoverCheck 9 (childHH (childLL (childHH (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHH (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHH (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100330310 :
    adaptiveCoverCheck 9 (childLL (childLH (childHH (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childHH (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHH (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100330311 :
    adaptiveCoverCheck 9 (childLH (childLH (childHH (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childHH (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHH (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100330312 :
    adaptiveCoverCheck 9 (childHL (childLH (childHH (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHH (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHH (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100330313 :
    adaptiveCoverCheck 9 (childHH (childLH (childHH (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHH (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHH (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100330320 :
    adaptiveCoverCheck 9 (childLL (childHL (childHH (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childHH (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childHH (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100330321 :
    adaptiveCoverCheck 9 (childLH (childHL (childHH (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childHH (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childHH (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100330322 :
    adaptiveCoverCheck 9 (childHL (childHL (childHH (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childHH (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childHH (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100330323 :
    adaptiveCoverCheck 9 (childHH (childHL (childHH (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childHH (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childHH (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100330330 :
    adaptiveCoverCheck 9 (childLL (childHH (childHH (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childHH (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childHH (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100330331 :
    adaptiveCoverCheck 9 (childLH (childHH (childHH (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childHH (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childHH (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100330332 :
    adaptiveCoverCheck 9 (childHL (childHH (childHH (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childHH (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childHH (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100330333 :
    adaptiveCoverCheck 9 (childHH (childHH (childHH (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childHH (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childHH (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010033100 :
    adaptiveCoverCheck 10 (childLL (childLL (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010033101 :
    adaptiveCoverCheck 10 (childLH (childLL (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100331020 :
    adaptiveCoverCheck 9 (childLL (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100331021 :
    adaptiveCoverCheck 9 (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100331022 :
    adaptiveCoverCheck 9 (childHL (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100331023 :
    adaptiveCoverCheck 9 (childHH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100331030 :
    adaptiveCoverCheck 9 (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100331031 :
    adaptiveCoverCheck 9 (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100331032 :
    adaptiveCoverCheck 9 (childHL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100331033 :
    adaptiveCoverCheck 9 (childHH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010033110 :
    adaptiveCoverCheck 10 (childLL (childLH (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010033111 :
    adaptiveCoverCheck 10 (childLH (childLH (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100331120 :
    adaptiveCoverCheck 9 (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100331121 :
    adaptiveCoverCheck 9 (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100331122 :
    adaptiveCoverCheck 9 (childHL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100331123 :
    adaptiveCoverCheck 9 (childHH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100331130 :
    adaptiveCoverCheck 9 (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100331131 :
    adaptiveCoverCheck 9 (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100331132 :
    adaptiveCoverCheck 9 (childHL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100331133 :
    adaptiveCoverCheck 9 (childHH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100331200 :
    adaptiveCoverCheck 9 (childLL (childLL (childHL (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHL (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHL (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100331201 :
    adaptiveCoverCheck 9 (childLH (childLL (childHL (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHL (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHL (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100331202 :
    adaptiveCoverCheck 9 (childHL (childLL (childHL (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHL (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHL (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100331203 :
    adaptiveCoverCheck 9 (childHH (childLL (childHL (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHL (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHL (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100331210 :
    adaptiveCoverCheck 9 (childLL (childLH (childHL (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childHL (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHL (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100331211 :
    adaptiveCoverCheck 9 (childLH (childLH (childHL (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childHL (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHL (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100331212 :
    adaptiveCoverCheck 9 (childHL (childLH (childHL (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHL (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHL (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100331213 :
    adaptiveCoverCheck 9 (childHH (childLH (childHL (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHL (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHL (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100331220 :
    adaptiveCoverCheck 9 (childLL (childHL (childHL (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childHL (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childHL (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100331221 :
    adaptiveCoverCheck 9 (childLH (childHL (childHL (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childHL (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childHL (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100331222 :
    adaptiveCoverCheck 9 (childHL (childHL (childHL (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childHL (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childHL (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100331223 :
    adaptiveCoverCheck 9 (childHH (childHL (childHL (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childHL (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childHL (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100331230 :
    adaptiveCoverCheck 9 (childLL (childHH (childHL (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childHL (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childHL (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100331231 :
    adaptiveCoverCheck 9 (childLH (childHH (childHL (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childHL (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childHL (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100331232 :
    adaptiveCoverCheck 9 (childHL (childHH (childHL (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childHL (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childHL (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100331233 :
    adaptiveCoverCheck 9 (childHH (childHH (childHL (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childHL (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childHL (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100331300 :
    adaptiveCoverCheck 9 (childLL (childLL (childHH (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHH (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHH (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100331301 :
    adaptiveCoverCheck 9 (childLH (childLL (childHH (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHH (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHH (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100331302 :
    adaptiveCoverCheck 9 (childHL (childLL (childHH (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHH (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHH (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100331303 :
    adaptiveCoverCheck 9 (childHH (childLL (childHH (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHH (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHH (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100331310 :
    adaptiveCoverCheck 9 (childLL (childLH (childHH (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childHH (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHH (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100331311 :
    adaptiveCoverCheck 9 (childLH (childLH (childHH (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childHH (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHH (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100331312 :
    adaptiveCoverCheck 9 (childHL (childLH (childHH (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHH (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHH (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100331313 :
    adaptiveCoverCheck 9 (childHH (childLH (childHH (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHH (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHH (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100331320 :
    adaptiveCoverCheck 9 (childLL (childHL (childHH (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childHH (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childHH (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100331321 :
    adaptiveCoverCheck 9 (childLH (childHL (childHH (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childHH (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childHH (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100331322 :
    adaptiveCoverCheck 9 (childHL (childHL (childHH (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childHH (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childHH (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100331323 :
    adaptiveCoverCheck 9 (childHH (childHL (childHH (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childHH (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childHH (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100331330 :
    adaptiveCoverCheck 9 (childLL (childHH (childHH (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childHH (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childHH (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100331331 :
    adaptiveCoverCheck 9 (childLH (childHH (childHH (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childHH (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childHH (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100331332 :
    adaptiveCoverCheck 9 (childHL (childHH (childHH (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childHH (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childHH (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100331333 :
    adaptiveCoverCheck 9 (childHH (childHH (childHH (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childHH (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childHH (childLH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01003320 :
    adaptiveCoverCheck 11 (childLL (childHL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childHL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01003321 :
    adaptiveCoverCheck 11 (childLH (childHL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childHL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01003322 :
    adaptiveCoverCheck 11 (childHL (childHL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01003323 :
    adaptiveCoverCheck 11 (childHH (childHL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010033300 :
    adaptiveCoverCheck 10 (childLL (childLL (childHH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childHH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childHH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010033301 :
    adaptiveCoverCheck 10 (childLH (childLL (childHH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childHH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childHH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010033302 :
    adaptiveCoverCheck 10 (childHL (childLL (childHH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLL (childHH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childHH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010033303 :
    adaptiveCoverCheck 10 (childHH (childLL (childHH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLL (childHH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childHH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010033310 :
    adaptiveCoverCheck 10 (childLL (childLH (childHH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childHH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childHH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010033311 :
    adaptiveCoverCheck 10 (childLH (childLH (childHH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childHH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childHH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010033312 :
    adaptiveCoverCheck 10 (childHL (childLH (childHH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLH (childHH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childHH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010033313 :
    adaptiveCoverCheck 10 (childHH (childLH (childHH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLH (childHH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childHH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01003332 :
    adaptiveCoverCheck 11 (childHL (childHH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01003333 :
    adaptiveCoverCheck 11 (childHH (childHH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010100 :
    adaptiveCoverCheck 13 (childLL (childLL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))) = true := by
  have h : ((childLL (childLL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL (childLL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010101 :
    adaptiveCoverCheck 13 (childLH (childLL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))) = true := by
  have h : ((childLH (childLL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH (childLL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010102 :
    adaptiveCoverCheck 13 (childHL (childLL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))) = true := by
  have h : ((childHL (childLL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010103 :
    adaptiveCoverCheck 13 (childHH (childLL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))) = true := by
  have h : ((childHH (childLL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010110 :
    adaptiveCoverCheck 13 (childLL (childLH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))) = true := by
  have h : ((childLL (childLH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL (childLH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010111 :
    adaptiveCoverCheck 13 (childLH (childLH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))) = true := by
  have h : ((childLH (childLH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH (childLH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010112 :
    adaptiveCoverCheck 13 (childHL (childLH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))) = true := by
  have h : ((childHL (childLH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010113 :
    adaptiveCoverCheck 13 (childHH (childLH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))) = true := by
  have h : ((childHH (childLH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101200 :
    adaptiveCoverCheck 12 (childLL (childLL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childLL (childLL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101201 :
    adaptiveCoverCheck 12 (childLH (childLL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childLH (childLL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01012020 :
    adaptiveCoverCheck 11 (childLL (childHL (childLL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childHL (childLL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHL (childLL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01012021 :
    adaptiveCoverCheck 11 (childLH (childHL (childLL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childHL (childLL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHL (childLL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01012022 :
    adaptiveCoverCheck 11 (childHL (childHL (childLL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHL (childLL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childLL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01012023 :
    adaptiveCoverCheck 11 (childHH (childHL (childLL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHL (childLL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childLL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01012030 :
    adaptiveCoverCheck 11 (childLL (childHH (childLL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childHH (childLL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHH (childLL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01012031 :
    adaptiveCoverCheck 11 (childLH (childHH (childLL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childHH (childLL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHH (childLL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01012032 :
    adaptiveCoverCheck 11 (childHL (childHH (childLL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHH (childLL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childLL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01012033 :
    adaptiveCoverCheck 11 (childHH (childHH (childLL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHH (childLL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childLL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101210 :
    adaptiveCoverCheck 12 (childLL (childLH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childLL (childLH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101211 :
    adaptiveCoverCheck 12 (childLH (childLH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childLH (childLH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01012120 :
    adaptiveCoverCheck 11 (childLL (childHL (childLH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childHL (childLH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHL (childLH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01012121 :
    adaptiveCoverCheck 11 (childLH (childHL (childLH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childHL (childLH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHL (childLH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01012122 :
    adaptiveCoverCheck 11 (childHL (childHL (childLH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHL (childLH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childLH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01012123 :
    adaptiveCoverCheck 11 (childHH (childHL (childLH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHL (childLH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childLH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01012130 :
    adaptiveCoverCheck 11 (childLL (childHH (childLH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childHH (childLH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHH (childLH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01012131 :
    adaptiveCoverCheck 11 (childLH (childHH (childLH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childHH (childLH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHH (childLH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01012132 :
    adaptiveCoverCheck 11 (childHL (childHH (childLH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHH (childLH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childLH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01012133 :
    adaptiveCoverCheck 11 (childHH (childHH (childLH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHH (childLH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childLH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010122000 :
    adaptiveCoverCheck 10 (childLL (childLL (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010122001 :
    adaptiveCoverCheck 10 (childLH (childLL (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101220020 :
    adaptiveCoverCheck 9 (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101220021 :
    adaptiveCoverCheck 9 (childLH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101220022 :
    adaptiveCoverCheck 9 (childHL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101220023 :
    adaptiveCoverCheck 9 (childHH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101220030 :
    adaptiveCoverCheck 9 (childLL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101220031 :
    adaptiveCoverCheck 9 (childLH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101220032 :
    adaptiveCoverCheck 9 (childHL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101220033 :
    adaptiveCoverCheck 9 (childHH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010122010 :
    adaptiveCoverCheck 10 (childLL (childLH (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010122011 :
    adaptiveCoverCheck 10 (childLH (childLH (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101220120 :
    adaptiveCoverCheck 9 (childLL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101220121 :
    adaptiveCoverCheck 9 (childLH (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101220122 :
    adaptiveCoverCheck 9 (childHL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101220123 :
    adaptiveCoverCheck 9 (childHH (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101220130 :
    adaptiveCoverCheck 9 (childLL (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101220131 :
    adaptiveCoverCheck 9 (childLH (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101220132 :
    adaptiveCoverCheck 9 (childHL (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101220133 :
    adaptiveCoverCheck 9 (childHH (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101220200 :
    adaptiveCoverCheck 9 (childLL (childLL (childHL (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHL (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHL (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101220201 :
    adaptiveCoverCheck 9 (childLH (childLL (childHL (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHL (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHL (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101220202 :
    adaptiveCoverCheck 9 (childHL (childLL (childHL (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHL (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHL (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101220203 :
    adaptiveCoverCheck 9 (childHH (childLL (childHL (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHL (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHL (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101220210 :
    adaptiveCoverCheck 9 (childLL (childLH (childHL (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childHL (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHL (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101220211 :
    adaptiveCoverCheck 9 (childLH (childLH (childHL (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childHL (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHL (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101220212 :
    adaptiveCoverCheck 9 (childHL (childLH (childHL (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHL (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHL (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101220213 :
    adaptiveCoverCheck 9 (childHH (childLH (childHL (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHL (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHL (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101220220 :
    adaptiveCoverCheck 9 (childLL (childHL (childHL (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childHL (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childHL (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101220221 :
    adaptiveCoverCheck 9 (childLH (childHL (childHL (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childHL (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childHL (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101220222 :
    adaptiveCoverCheck 9 (childHL (childHL (childHL (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childHL (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childHL (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101220223 :
    adaptiveCoverCheck 9 (childHH (childHL (childHL (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childHL (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childHL (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101220230 :
    adaptiveCoverCheck 9 (childLL (childHH (childHL (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childHL (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childHL (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101220231 :
    adaptiveCoverCheck 9 (childLH (childHH (childHL (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childHL (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childHL (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101220232 :
    adaptiveCoverCheck 9 (childHL (childHH (childHL (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childHL (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childHL (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101220233 :
    adaptiveCoverCheck 9 (childHH (childHH (childHL (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childHL (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childHL (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101220300 :
    adaptiveCoverCheck 9 (childLL (childLL (childHH (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHH (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHH (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101220301 :
    adaptiveCoverCheck 9 (childLH (childLL (childHH (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHH (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHH (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101220302 :
    adaptiveCoverCheck 9 (childHL (childLL (childHH (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHH (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHH (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101220303 :
    adaptiveCoverCheck 9 (childHH (childLL (childHH (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHH (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHH (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101220310 :
    adaptiveCoverCheck 9 (childLL (childLH (childHH (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childHH (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHH (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101220311 :
    adaptiveCoverCheck 9 (childLH (childLH (childHH (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childHH (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHH (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101220312 :
    adaptiveCoverCheck 9 (childHL (childLH (childHH (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHH (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHH (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101220313 :
    adaptiveCoverCheck 9 (childHH (childLH (childHH (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHH (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHH (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101220320 :
    adaptiveCoverCheck 9 (childLL (childHL (childHH (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childHH (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childHH (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101220321 :
    adaptiveCoverCheck 9 (childLH (childHL (childHH (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childHH (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childHH (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101220322 :
    adaptiveCoverCheck 9 (childHL (childHL (childHH (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childHH (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childHH (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101220323 :
    adaptiveCoverCheck 9 (childHH (childHL (childHH (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childHH (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childHH (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101220330 :
    adaptiveCoverCheck 9 (childLL (childHH (childHH (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childHH (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childHH (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101220331 :
    adaptiveCoverCheck 9 (childLH (childHH (childHH (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childHH (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childHH (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101220332 :
    adaptiveCoverCheck 9 (childHL (childHH (childHH (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childHH (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childHH (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101220333 :
    adaptiveCoverCheck 9 (childHH (childHH (childHH (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childHH (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childHH (childLL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010122100 :
    adaptiveCoverCheck 10 (childLL (childLL (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010122101 :
    adaptiveCoverCheck 10 (childLH (childLL (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101221020 :
    adaptiveCoverCheck 9 (childLL (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101221021 :
    adaptiveCoverCheck 9 (childLH (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101221022 :
    adaptiveCoverCheck 9 (childHL (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101221023 :
    adaptiveCoverCheck 9 (childHH (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101221030 :
    adaptiveCoverCheck 9 (childLL (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101221031 :
    adaptiveCoverCheck 9 (childLH (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101221032 :
    adaptiveCoverCheck 9 (childHL (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101221033 :
    adaptiveCoverCheck 9 (childHH (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010122110 :
    adaptiveCoverCheck 10 (childLL (childLH (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010122111 :
    adaptiveCoverCheck 10 (childLH (childLH (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101221120 :
    adaptiveCoverCheck 9 (childLL (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101221121 :
    adaptiveCoverCheck 9 (childLH (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101221122 :
    adaptiveCoverCheck 9 (childHL (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101221123 :
    adaptiveCoverCheck 9 (childHH (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101221130 :
    adaptiveCoverCheck 9 (childLL (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101221131 :
    adaptiveCoverCheck 9 (childLH (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101221132 :
    adaptiveCoverCheck 9 (childHL (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101221133 :
    adaptiveCoverCheck 9 (childHH (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101221200 :
    adaptiveCoverCheck 9 (childLL (childLL (childHL (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHL (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHL (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101221201 :
    adaptiveCoverCheck 9 (childLH (childLL (childHL (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHL (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHL (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101221202 :
    adaptiveCoverCheck 9 (childHL (childLL (childHL (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHL (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHL (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101221203 :
    adaptiveCoverCheck 9 (childHH (childLL (childHL (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHL (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHL (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101221210 :
    adaptiveCoverCheck 9 (childLL (childLH (childHL (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childHL (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHL (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101221211 :
    adaptiveCoverCheck 9 (childLH (childLH (childHL (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childHL (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHL (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101221212 :
    adaptiveCoverCheck 9 (childHL (childLH (childHL (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHL (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHL (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101221213 :
    adaptiveCoverCheck 9 (childHH (childLH (childHL (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHL (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHL (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101221220 :
    adaptiveCoverCheck 9 (childLL (childHL (childHL (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childHL (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childHL (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101221221 :
    adaptiveCoverCheck 9 (childLH (childHL (childHL (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childHL (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childHL (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101221222 :
    adaptiveCoverCheck 9 (childHL (childHL (childHL (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childHL (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childHL (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101221223 :
    adaptiveCoverCheck 9 (childHH (childHL (childHL (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childHL (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childHL (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101221230 :
    adaptiveCoverCheck 9 (childLL (childHH (childHL (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childHL (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childHL (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101221231 :
    adaptiveCoverCheck 9 (childLH (childHH (childHL (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childHL (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childHL (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101221232 :
    adaptiveCoverCheck 9 (childHL (childHH (childHL (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childHL (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childHL (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101221233 :
    adaptiveCoverCheck 9 (childHH (childHH (childHL (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childHL (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childHL (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101221300 :
    adaptiveCoverCheck 9 (childLL (childLL (childHH (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHH (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHH (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101221301 :
    adaptiveCoverCheck 9 (childLH (childLL (childHH (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHH (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHH (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101221302 :
    adaptiveCoverCheck 9 (childHL (childLL (childHH (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHH (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHH (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101221303 :
    adaptiveCoverCheck 9 (childHH (childLL (childHH (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHH (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHH (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101221310 :
    adaptiveCoverCheck 9 (childLL (childLH (childHH (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childHH (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHH (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101221311 :
    adaptiveCoverCheck 9 (childLH (childLH (childHH (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childHH (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHH (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101221312 :
    adaptiveCoverCheck 9 (childHL (childLH (childHH (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHH (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHH (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101221313 :
    adaptiveCoverCheck 9 (childHH (childLH (childHH (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHH (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHH (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101221320 :
    adaptiveCoverCheck 9 (childLL (childHL (childHH (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childHH (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childHH (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101221321 :
    adaptiveCoverCheck 9 (childLH (childHL (childHH (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childHH (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childHH (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101221322 :
    adaptiveCoverCheck 9 (childHL (childHL (childHH (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childHH (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childHH (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101221323 :
    adaptiveCoverCheck 9 (childHH (childHL (childHH (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childHH (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childHH (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101221330 :
    adaptiveCoverCheck 9 (childLL (childHH (childHH (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childHH (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childHH (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101221331 :
    adaptiveCoverCheck 9 (childLH (childHH (childHH (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childHH (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childHH (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101221332 :
    adaptiveCoverCheck 9 (childHL (childHH (childHH (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childHH (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childHH (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101221333 :
    adaptiveCoverCheck 9 (childHH (childHH (childHH (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childHH (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childHH (childLH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010122200 :
    adaptiveCoverCheck 10 (childLL (childLL (childHL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childHL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childHL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010122201 :
    adaptiveCoverCheck 10 (childLH (childLL (childHL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childHL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childHL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010122202 :
    adaptiveCoverCheck 10 (childHL (childLL (childHL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLL (childHL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childHL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010122203 :
    adaptiveCoverCheck 10 (childHH (childLL (childHL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLL (childHL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childHL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010122210 :
    adaptiveCoverCheck 10 (childLL (childLH (childHL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childHL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childHL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010122211 :
    adaptiveCoverCheck 10 (childLH (childLH (childHL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childHL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childHL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010122212 :
    adaptiveCoverCheck 10 (childHL (childLH (childHL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLH (childHL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childHL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010122213 :
    adaptiveCoverCheck 10 (childHH (childLH (childHL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLH (childHL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childHL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01012222 :
    adaptiveCoverCheck 11 (childHL (childHL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01012223 :
    adaptiveCoverCheck 11 (childHH (childHL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010122300 :
    adaptiveCoverCheck 10 (childLL (childLL (childHH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childHH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childHH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010122301 :
    adaptiveCoverCheck 10 (childLH (childLL (childHH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childHH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childHH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010122302 :
    adaptiveCoverCheck 10 (childHL (childLL (childHH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLL (childHH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childHH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010122303 :
    adaptiveCoverCheck 10 (childHH (childLL (childHH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLL (childHH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childHH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010122310 :
    adaptiveCoverCheck 10 (childLL (childLH (childHH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childHH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childHH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010122311 :
    adaptiveCoverCheck 10 (childLH (childLH (childHH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childHH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childHH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010122312 :
    adaptiveCoverCheck 10 (childHL (childLH (childHH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLH (childHH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childHH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010122313 :
    adaptiveCoverCheck 10 (childHH (childLH (childHH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLH (childHH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childHH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01012232 :
    adaptiveCoverCheck 11 (childHL (childHH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01012233 :
    adaptiveCoverCheck 11 (childHH (childHH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childHL (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010123000 :
    adaptiveCoverCheck 10 (childLL (childLL (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010123001 :
    adaptiveCoverCheck 10 (childLH (childLL (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101230020 :
    adaptiveCoverCheck 9 (childLL (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101230021 :
    adaptiveCoverCheck 9 (childLH (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101230022 :
    adaptiveCoverCheck 9 (childHL (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101230023 :
    adaptiveCoverCheck 9 (childHH (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101230030 :
    adaptiveCoverCheck 9 (childLL (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101230031 :
    adaptiveCoverCheck 9 (childLH (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101230032 :
    adaptiveCoverCheck 9 (childHL (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101230033 :
    adaptiveCoverCheck 9 (childHH (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010123010 :
    adaptiveCoverCheck 10 (childLL (childLH (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010123011 :
    adaptiveCoverCheck 10 (childLH (childLH (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101230120 :
    adaptiveCoverCheck 9 (childLL (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101230121 :
    adaptiveCoverCheck 9 (childLH (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101230122 :
    adaptiveCoverCheck 9 (childHL (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101230123 :
    adaptiveCoverCheck 9 (childHH (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101230130 :
    adaptiveCoverCheck 9 (childLL (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101230131 :
    adaptiveCoverCheck 9 (childLH (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101230132 :
    adaptiveCoverCheck 9 (childHL (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101230133 :
    adaptiveCoverCheck 9 (childHH (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101230200 :
    adaptiveCoverCheck 9 (childLL (childLL (childHL (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHL (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHL (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101230201 :
    adaptiveCoverCheck 9 (childLH (childLL (childHL (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHL (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHL (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101230202 :
    adaptiveCoverCheck 9 (childHL (childLL (childHL (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHL (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHL (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101230203 :
    adaptiveCoverCheck 9 (childHH (childLL (childHL (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHL (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHL (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101230210 :
    adaptiveCoverCheck 9 (childLL (childLH (childHL (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childHL (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHL (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101230211 :
    adaptiveCoverCheck 9 (childLH (childLH (childHL (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childHL (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHL (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101230212 :
    adaptiveCoverCheck 9 (childHL (childLH (childHL (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHL (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHL (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101230213 :
    adaptiveCoverCheck 9 (childHH (childLH (childHL (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHL (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHL (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101230220 :
    adaptiveCoverCheck 9 (childLL (childHL (childHL (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childHL (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childHL (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101230221 :
    adaptiveCoverCheck 9 (childLH (childHL (childHL (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childHL (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childHL (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101230222 :
    adaptiveCoverCheck 9 (childHL (childHL (childHL (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childHL (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childHL (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101230223 :
    adaptiveCoverCheck 9 (childHH (childHL (childHL (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childHL (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childHL (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101230230 :
    adaptiveCoverCheck 9 (childLL (childHH (childHL (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childHL (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childHL (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101230231 :
    adaptiveCoverCheck 9 (childLH (childHH (childHL (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childHL (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childHL (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101230232 :
    adaptiveCoverCheck 9 (childHL (childHH (childHL (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childHL (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childHL (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101230233 :
    adaptiveCoverCheck 9 (childHH (childHH (childHL (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childHL (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childHL (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101230300 :
    adaptiveCoverCheck 9 (childLL (childLL (childHH (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHH (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHH (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101230301 :
    adaptiveCoverCheck 9 (childLH (childLL (childHH (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHH (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHH (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101230302 :
    adaptiveCoverCheck 9 (childHL (childLL (childHH (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHH (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHH (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101230303 :
    adaptiveCoverCheck 9 (childHH (childLL (childHH (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHH (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHH (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101230310 :
    adaptiveCoverCheck 9 (childLL (childLH (childHH (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childHH (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHH (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101230311 :
    adaptiveCoverCheck 9 (childLH (childLH (childHH (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childHH (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHH (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101230312 :
    adaptiveCoverCheck 9 (childHL (childLH (childHH (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHH (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHH (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101230313 :
    adaptiveCoverCheck 9 (childHH (childLH (childHH (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHH (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHH (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101230320 :
    adaptiveCoverCheck 9 (childLL (childHL (childHH (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childHH (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childHH (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101230321 :
    adaptiveCoverCheck 9 (childLH (childHL (childHH (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childHH (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childHH (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101230322 :
    adaptiveCoverCheck 9 (childHL (childHL (childHH (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childHH (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childHH (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101230323 :
    adaptiveCoverCheck 9 (childHH (childHL (childHH (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childHH (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childHH (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101230330 :
    adaptiveCoverCheck 9 (childLL (childHH (childHH (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childHH (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childHH (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101230331 :
    adaptiveCoverCheck 9 (childLH (childHH (childHH (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childHH (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childHH (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101230332 :
    adaptiveCoverCheck 9 (childHL (childHH (childHH (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childHH (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childHH (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101230333 :
    adaptiveCoverCheck 9 (childHH (childHH (childHH (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childHH (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childHH (childLL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010123100 :
    adaptiveCoverCheck 10 (childLL (childLL (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010123101 :
    adaptiveCoverCheck 10 (childLH (childLL (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101231020 :
    adaptiveCoverCheck 9 (childLL (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101231021 :
    adaptiveCoverCheck 9 (childLH (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101231022 :
    adaptiveCoverCheck 9 (childHL (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101231023 :
    adaptiveCoverCheck 9 (childHH (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101231030 :
    adaptiveCoverCheck 9 (childLL (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101231031 :
    adaptiveCoverCheck 9 (childLH (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101231032 :
    adaptiveCoverCheck 9 (childHL (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101231033 :
    adaptiveCoverCheck 9 (childHH (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010123110 :
    adaptiveCoverCheck 10 (childLL (childLH (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010123111 :
    adaptiveCoverCheck 10 (childLH (childLH (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101231120 :
    adaptiveCoverCheck 9 (childLL (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101231121 :
    adaptiveCoverCheck 9 (childLH (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101231122 :
    adaptiveCoverCheck 9 (childHL (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101231123 :
    adaptiveCoverCheck 9 (childHH (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101231130 :
    adaptiveCoverCheck 9 (childLL (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101231131 :
    adaptiveCoverCheck 9 (childLH (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101231132 :
    adaptiveCoverCheck 9 (childHL (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101231133 :
    adaptiveCoverCheck 9 (childHH (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101231200 :
    adaptiveCoverCheck 9 (childLL (childLL (childHL (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHL (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHL (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101231201 :
    adaptiveCoverCheck 9 (childLH (childLL (childHL (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHL (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHL (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101231202 :
    adaptiveCoverCheck 9 (childHL (childLL (childHL (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHL (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHL (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101231203 :
    adaptiveCoverCheck 9 (childHH (childLL (childHL (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHL (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHL (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101231210 :
    adaptiveCoverCheck 9 (childLL (childLH (childHL (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childHL (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHL (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101231211 :
    adaptiveCoverCheck 9 (childLH (childLH (childHL (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childHL (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHL (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101231212 :
    adaptiveCoverCheck 9 (childHL (childLH (childHL (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHL (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHL (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101231213 :
    adaptiveCoverCheck 9 (childHH (childLH (childHL (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHL (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHL (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101231220 :
    adaptiveCoverCheck 9 (childLL (childHL (childHL (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childHL (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childHL (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101231221 :
    adaptiveCoverCheck 9 (childLH (childHL (childHL (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childHL (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childHL (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101231222 :
    adaptiveCoverCheck 9 (childHL (childHL (childHL (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childHL (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childHL (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101231223 :
    adaptiveCoverCheck 9 (childHH (childHL (childHL (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childHL (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childHL (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101231230 :
    adaptiveCoverCheck 9 (childLL (childHH (childHL (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childHL (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childHL (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101231231 :
    adaptiveCoverCheck 9 (childLH (childHH (childHL (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childHL (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childHL (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101231232 :
    adaptiveCoverCheck 9 (childHL (childHH (childHL (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childHL (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childHL (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101231233 :
    adaptiveCoverCheck 9 (childHH (childHH (childHL (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childHL (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childHL (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101231300 :
    adaptiveCoverCheck 9 (childLL (childLL (childHH (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHH (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHH (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101231301 :
    adaptiveCoverCheck 9 (childLH (childLL (childHH (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHH (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHH (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101231302 :
    adaptiveCoverCheck 9 (childHL (childLL (childHH (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHH (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHH (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101231303 :
    adaptiveCoverCheck 9 (childHH (childLL (childHH (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHH (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHH (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101231310 :
    adaptiveCoverCheck 9 (childLL (childLH (childHH (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childHH (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHH (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101231311 :
    adaptiveCoverCheck 9 (childLH (childLH (childHH (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childHH (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHH (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101231312 :
    adaptiveCoverCheck 9 (childHL (childLH (childHH (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHH (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHH (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101231313 :
    adaptiveCoverCheck 9 (childHH (childLH (childHH (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHH (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHH (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101231320 :
    adaptiveCoverCheck 9 (childLL (childHL (childHH (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childHH (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childHH (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101231321 :
    adaptiveCoverCheck 9 (childLH (childHL (childHH (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childHH (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childHH (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101231322 :
    adaptiveCoverCheck 9 (childHL (childHL (childHH (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childHH (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childHH (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101231323 :
    adaptiveCoverCheck 9 (childHH (childHL (childHH (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childHH (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childHH (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101231330 :
    adaptiveCoverCheck 9 (childLL (childHH (childHH (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childHH (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childHH (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101231331 :
    adaptiveCoverCheck 9 (childLH (childHH (childHH (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childHH (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childHH (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101231332 :
    adaptiveCoverCheck 9 (childHL (childHH (childHH (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childHH (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childHH (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101231333 :
    adaptiveCoverCheck 9 (childHH (childHH (childHH (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childHH (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childHH (childLH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010123200 :
    adaptiveCoverCheck 10 (childLL (childLL (childHL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childHL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childHL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010123201 :
    adaptiveCoverCheck 10 (childLH (childLL (childHL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childHL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childHL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010123202 :
    adaptiveCoverCheck 10 (childHL (childLL (childHL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLL (childHL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childHL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010123203 :
    adaptiveCoverCheck 10 (childHH (childLL (childHL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLL (childHL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childHL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010123210 :
    adaptiveCoverCheck 10 (childLL (childLH (childHL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childHL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childHL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010123211 :
    adaptiveCoverCheck 10 (childLH (childLH (childHL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childHL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childHL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010123212 :
    adaptiveCoverCheck 10 (childHL (childLH (childHL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLH (childHL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childHL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010123213 :
    adaptiveCoverCheck 10 (childHH (childLH (childHL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLH (childHL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childHL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01012322 :
    adaptiveCoverCheck 11 (childHL (childHL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01012323 :
    adaptiveCoverCheck 11 (childHH (childHL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010123300 :
    adaptiveCoverCheck 10 (childLL (childLL (childHH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childHH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childHH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010123301 :
    adaptiveCoverCheck 10 (childLH (childLL (childHH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childHH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childHH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010123302 :
    adaptiveCoverCheck 10 (childHL (childLL (childHH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLL (childHH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childHH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010123303 :
    adaptiveCoverCheck 10 (childHH (childLL (childHH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLL (childHH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childHH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010123310 :
    adaptiveCoverCheck 10 (childLL (childLH (childHH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childHH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childHH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010123311 :
    adaptiveCoverCheck 10 (childLH (childLH (childHH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childHH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childHH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010123312 :
    adaptiveCoverCheck 10 (childHL (childLH (childHH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLH (childHH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childHH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010123313 :
    adaptiveCoverCheck 10 (childHH (childLH (childHH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLH (childHH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childHH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01012332 :
    adaptiveCoverCheck 11 (childHL (childHH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01012333 :
    adaptiveCoverCheck 11 (childHH (childHH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childHH (childHL (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101300 :
    adaptiveCoverCheck 12 (childLL (childLL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childLL (childLL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101301 :
    adaptiveCoverCheck 12 (childLH (childLL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childLH (childLL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01013020 :
    adaptiveCoverCheck 11 (childLL (childHL (childLL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childHL (childLL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHL (childLL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01013021 :
    adaptiveCoverCheck 11 (childLH (childHL (childLL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childHL (childLL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHL (childLL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01013022 :
    adaptiveCoverCheck 11 (childHL (childHL (childLL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHL (childLL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childLL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01013023 :
    adaptiveCoverCheck 11 (childHH (childHL (childLL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHL (childLL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childLL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01013030 :
    adaptiveCoverCheck 11 (childLL (childHH (childLL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childHH (childLL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHH (childLL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01013031 :
    adaptiveCoverCheck 11 (childLH (childHH (childLL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childHH (childLL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHH (childLL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01013032 :
    adaptiveCoverCheck 11 (childHL (childHH (childLL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHH (childLL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childLL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01013033 :
    adaptiveCoverCheck 11 (childHH (childHH (childLL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHH (childLL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childLL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101310 :
    adaptiveCoverCheck 12 (childLL (childLH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childLL (childLH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101311 :
    adaptiveCoverCheck 12 (childLH (childLH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childLH (childLH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01013120 :
    adaptiveCoverCheck 11 (childLL (childHL (childLH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childHL (childLH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHL (childLH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01013121 :
    adaptiveCoverCheck 11 (childLH (childHL (childLH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childHL (childLH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHL (childLH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01013122 :
    adaptiveCoverCheck 11 (childHL (childHL (childLH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHL (childLH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childLH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01013123 :
    adaptiveCoverCheck 11 (childHH (childHL (childLH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHL (childLH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childLH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01013130 :
    adaptiveCoverCheck 11 (childLL (childHH (childLH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childHH (childLH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHH (childLH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01013131 :
    adaptiveCoverCheck 11 (childLH (childHH (childLH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childHH (childLH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHH (childLH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01013132 :
    adaptiveCoverCheck 11 (childHL (childHH (childLH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHH (childLH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childLH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01013133 :
    adaptiveCoverCheck 11 (childHH (childHH (childLH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHH (childLH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childLH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010132000 :
    adaptiveCoverCheck 10 (childLL (childLL (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010132001 :
    adaptiveCoverCheck 10 (childLH (childLL (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101320020 :
    adaptiveCoverCheck 9 (childLL (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101320021 :
    adaptiveCoverCheck 9 (childLH (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101320022 :
    adaptiveCoverCheck 9 (childHL (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101320023 :
    adaptiveCoverCheck 9 (childHH (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101320030 :
    adaptiveCoverCheck 9 (childLL (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101320031 :
    adaptiveCoverCheck 9 (childLH (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101320032 :
    adaptiveCoverCheck 9 (childHL (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101320033 :
    adaptiveCoverCheck 9 (childHH (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010132010 :
    adaptiveCoverCheck 10 (childLL (childLH (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010132011 :
    adaptiveCoverCheck 10 (childLH (childLH (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101320120 :
    adaptiveCoverCheck 9 (childLL (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101320121 :
    adaptiveCoverCheck 9 (childLH (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101320122 :
    adaptiveCoverCheck 9 (childHL (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101320123 :
    adaptiveCoverCheck 9 (childHH (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101320130 :
    adaptiveCoverCheck 9 (childLL (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101320131 :
    adaptiveCoverCheck 9 (childLH (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101320132 :
    adaptiveCoverCheck 9 (childHL (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101320133 :
    adaptiveCoverCheck 9 (childHH (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101320200 :
    adaptiveCoverCheck 9 (childLL (childLL (childHL (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHL (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHL (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101320201 :
    adaptiveCoverCheck 9 (childLH (childLL (childHL (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHL (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHL (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101320202 :
    adaptiveCoverCheck 9 (childHL (childLL (childHL (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHL (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHL (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101320203 :
    adaptiveCoverCheck 9 (childHH (childLL (childHL (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHL (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHL (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101320210 :
    adaptiveCoverCheck 9 (childLL (childLH (childHL (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childHL (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHL (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101320211 :
    adaptiveCoverCheck 9 (childLH (childLH (childHL (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childHL (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHL (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101320212 :
    adaptiveCoverCheck 9 (childHL (childLH (childHL (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHL (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHL (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101320213 :
    adaptiveCoverCheck 9 (childHH (childLH (childHL (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHL (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHL (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101320220 :
    adaptiveCoverCheck 9 (childLL (childHL (childHL (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childHL (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childHL (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101320221 :
    adaptiveCoverCheck 9 (childLH (childHL (childHL (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childHL (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childHL (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101320222 :
    adaptiveCoverCheck 9 (childHL (childHL (childHL (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childHL (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childHL (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101320223 :
    adaptiveCoverCheck 9 (childHH (childHL (childHL (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childHL (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childHL (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101320230 :
    adaptiveCoverCheck 9 (childLL (childHH (childHL (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childHL (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childHL (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101320231 :
    adaptiveCoverCheck 9 (childLH (childHH (childHL (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childHL (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childHL (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101320232 :
    adaptiveCoverCheck 9 (childHL (childHH (childHL (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childHL (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childHL (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101320233 :
    adaptiveCoverCheck 9 (childHH (childHH (childHL (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childHL (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childHL (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101320300 :
    adaptiveCoverCheck 9 (childLL (childLL (childHH (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHH (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHH (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101320301 :
    adaptiveCoverCheck 9 (childLH (childLL (childHH (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHH (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHH (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101320302 :
    adaptiveCoverCheck 9 (childHL (childLL (childHH (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHH (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHH (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101320303 :
    adaptiveCoverCheck 9 (childHH (childLL (childHH (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHH (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHH (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101320310 :
    adaptiveCoverCheck 9 (childLL (childLH (childHH (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childHH (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHH (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101320311 :
    adaptiveCoverCheck 9 (childLH (childLH (childHH (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childHH (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHH (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101320312 :
    adaptiveCoverCheck 9 (childHL (childLH (childHH (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHH (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHH (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101320313 :
    adaptiveCoverCheck 9 (childHH (childLH (childHH (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHH (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHH (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101320320 :
    adaptiveCoverCheck 9 (childLL (childHL (childHH (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childHH (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childHH (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101320321 :
    adaptiveCoverCheck 9 (childLH (childHL (childHH (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childHH (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childHH (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101320322 :
    adaptiveCoverCheck 9 (childHL (childHL (childHH (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childHH (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childHH (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101320323 :
    adaptiveCoverCheck 9 (childHH (childHL (childHH (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childHH (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childHH (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101320330 :
    adaptiveCoverCheck 9 (childLL (childHH (childHH (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childHH (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childHH (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101320331 :
    adaptiveCoverCheck 9 (childLH (childHH (childHH (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childHH (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childHH (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101320332 :
    adaptiveCoverCheck 9 (childHL (childHH (childHH (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childHH (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childHH (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101320333 :
    adaptiveCoverCheck 9 (childHH (childHH (childHH (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childHH (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childHH (childLL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010132100 :
    adaptiveCoverCheck 10 (childLL (childLL (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010132101 :
    adaptiveCoverCheck 10 (childLH (childLL (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101321020 :
    adaptiveCoverCheck 9 (childLL (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101321021 :
    adaptiveCoverCheck 9 (childLH (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101321022 :
    adaptiveCoverCheck 9 (childHL (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101321023 :
    adaptiveCoverCheck 9 (childHH (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childLL (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101321030 :
    adaptiveCoverCheck 9 (childLL (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101321031 :
    adaptiveCoverCheck 9 (childLH (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101321032 :
    adaptiveCoverCheck 9 (childHL (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101321033 :
    adaptiveCoverCheck 9 (childHH (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childLL (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010132110 :
    adaptiveCoverCheck 10 (childLL (childLH (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010132111 :
    adaptiveCoverCheck 10 (childLH (childLH (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101321120 :
    adaptiveCoverCheck 9 (childLL (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101321121 :
    adaptiveCoverCheck 9 (childLH (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101321122 :
    adaptiveCoverCheck 9 (childHL (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101321123 :
    adaptiveCoverCheck 9 (childHH (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childLH (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101321130 :
    adaptiveCoverCheck 9 (childLL (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101321131 :
    adaptiveCoverCheck 9 (childLH (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101321132 :
    adaptiveCoverCheck 9 (childHL (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101321133 :
    adaptiveCoverCheck 9 (childHH (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childLH (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101321200 :
    adaptiveCoverCheck 9 (childLL (childLL (childHL (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHL (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHL (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101321201 :
    adaptiveCoverCheck 9 (childLH (childLL (childHL (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHL (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHL (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101321202 :
    adaptiveCoverCheck 9 (childHL (childLL (childHL (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHL (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHL (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101321203 :
    adaptiveCoverCheck 9 (childHH (childLL (childHL (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHL (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHL (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101321210 :
    adaptiveCoverCheck 9 (childLL (childLH (childHL (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childHL (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHL (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101321211 :
    adaptiveCoverCheck 9 (childLH (childLH (childHL (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childHL (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHL (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101321212 :
    adaptiveCoverCheck 9 (childHL (childLH (childHL (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHL (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHL (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101321213 :
    adaptiveCoverCheck 9 (childHH (childLH (childHL (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHL (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHL (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101321220 :
    adaptiveCoverCheck 9 (childLL (childHL (childHL (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childHL (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childHL (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101321221 :
    adaptiveCoverCheck 9 (childLH (childHL (childHL (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childHL (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childHL (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101321222 :
    adaptiveCoverCheck 9 (childHL (childHL (childHL (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childHL (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childHL (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101321223 :
    adaptiveCoverCheck 9 (childHH (childHL (childHL (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childHL (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childHL (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101321230 :
    adaptiveCoverCheck 9 (childLL (childHH (childHL (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childHL (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childHL (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101321231 :
    adaptiveCoverCheck 9 (childLH (childHH (childHL (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childHL (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childHL (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101321232 :
    adaptiveCoverCheck 9 (childHL (childHH (childHL (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childHL (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childHL (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101321233 :
    adaptiveCoverCheck 9 (childHH (childHH (childHL (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childHL (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childHL (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101321300 :
    adaptiveCoverCheck 9 (childLL (childLL (childHH (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHH (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHH (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101321301 :
    adaptiveCoverCheck 9 (childLH (childLL (childHH (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHH (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHH (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101321302 :
    adaptiveCoverCheck 9 (childHL (childLL (childHH (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHH (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHH (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101321303 :
    adaptiveCoverCheck 9 (childHH (childLL (childHH (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHH (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHH (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101321310 :
    adaptiveCoverCheck 9 (childLL (childLH (childHH (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childHH (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHH (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101321311 :
    adaptiveCoverCheck 9 (childLH (childLH (childHH (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childHH (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHH (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101321312 :
    adaptiveCoverCheck 9 (childHL (childLH (childHH (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHH (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHH (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101321313 :
    adaptiveCoverCheck 9 (childHH (childLH (childHH (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHH (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHH (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101321320 :
    adaptiveCoverCheck 9 (childLL (childHL (childHH (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childHH (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childHH (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101321321 :
    adaptiveCoverCheck 9 (childLH (childHL (childHH (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childHH (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childHH (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101321322 :
    adaptiveCoverCheck 9 (childHL (childHL (childHH (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childHH (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childHH (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101321323 :
    adaptiveCoverCheck 9 (childHH (childHL (childHH (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childHH (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childHH (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101321330 :
    adaptiveCoverCheck 9 (childLL (childHH (childHH (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childHH (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childHH (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101321331 :
    adaptiveCoverCheck 9 (childLH (childHH (childHH (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childHH (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childHH (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101321332 :
    adaptiveCoverCheck 9 (childHL (childHH (childHH (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childHH (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childHH (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101321333 :
    adaptiveCoverCheck 9 (childHH (childHH (childHH (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childHH (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childHH (childLH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010132200 :
    adaptiveCoverCheck 10 (childLL (childLL (childHL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childHL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childHL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010132201 :
    adaptiveCoverCheck 10 (childLH (childLL (childHL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childHL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childHL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010132202 :
    adaptiveCoverCheck 10 (childHL (childLL (childHL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLL (childHL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childHL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010132203 :
    adaptiveCoverCheck 10 (childHH (childLL (childHL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLL (childHL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childHL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010132210 :
    adaptiveCoverCheck 10 (childLL (childLH (childHL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childHL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childHL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010132211 :
    adaptiveCoverCheck 10 (childLH (childLH (childHL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childHL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childHL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010132212 :
    adaptiveCoverCheck 10 (childHL (childLH (childHL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLH (childHL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childHL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010132213 :
    adaptiveCoverCheck 10 (childHH (childLH (childHL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLH (childHL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childHL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01013222 :
    adaptiveCoverCheck 11 (childHL (childHL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01013223 :
    adaptiveCoverCheck 11 (childHH (childHL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010132300 :
    adaptiveCoverCheck 10 (childLL (childLL (childHH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childHH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childHH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010132301 :
    adaptiveCoverCheck 10 (childLH (childLL (childHH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childHH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childHH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010132302 :
    adaptiveCoverCheck 10 (childHL (childLL (childHH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLL (childHH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childHH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010132303 :
    adaptiveCoverCheck 10 (childHH (childLL (childHH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLL (childHH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childHH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010132310 :
    adaptiveCoverCheck 10 (childLL (childLH (childHH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childHH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childHH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010132311 :
    adaptiveCoverCheck 10 (childLH (childLH (childHH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childHH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childHH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010132312 :
    adaptiveCoverCheck 10 (childHL (childLH (childHH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLH (childHH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childHH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010132313 :
    adaptiveCoverCheck 10 (childHH (childLH (childHH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLH (childHH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childHH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01013232 :
    adaptiveCoverCheck 11 (childHL (childHH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01013233 :
    adaptiveCoverCheck 11 (childHH (childHH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010133000 :
    adaptiveCoverCheck 10 (childLL (childLL (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010133001 :
    adaptiveCoverCheck 10 (childLH (childLL (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101330020 :
    adaptiveCoverCheck 9 (childLL (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101330021 :
    adaptiveCoverCheck 9 (childLH (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101330022 :
    adaptiveCoverCheck 9 (childHL (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101330023 :
    adaptiveCoverCheck 9 (childHH (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childLL (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101330030 :
    adaptiveCoverCheck 9 (childLL (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101330031 :
    adaptiveCoverCheck 9 (childLH (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101330032 :
    adaptiveCoverCheck 9 (childHL (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101330033 :
    adaptiveCoverCheck 9 (childHH (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childLL (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

end PartE
end GerverSofa
