import GerverSofa.KernelOnly.PartE.E24KC2ProofHelpers

/-! E24KC5 checkpoint-aware kernel batch. -/
noncomputable section

namespace GerverSofa
namespace PartE

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf001123133 :
    adaptiveCoverCheck 10 (childHH (childHH (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHH (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00112320 :
    adaptiveCoverCheck 11 (childLL (childHL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childHL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00112321 :
    adaptiveCoverCheck 11 (childLH (childHL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childHL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00112322 :
    adaptiveCoverCheck 11 (childHL (childHL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00112323 :
    adaptiveCoverCheck 11 (childHH (childHL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00112330 :
    adaptiveCoverCheck 11 (childLL (childHH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childHH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00112331 :
    adaptiveCoverCheck 11 (childLH (childHH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childHH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00112332 :
    adaptiveCoverCheck 11 (childHL (childHH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00112333 :
    adaptiveCoverCheck 11 (childHH (childHH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0011300 :
    adaptiveCoverCheck 12 (childLL (childLL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childLL (childLL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0011301 :
    adaptiveCoverCheck 12 (childLH (childLL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childLH (childLL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00113020 :
    adaptiveCoverCheck 11 (childLL (childHL (childLL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childHL (childLL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHL (childLL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00113021 :
    adaptiveCoverCheck 11 (childLH (childHL (childLL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childHL (childLL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHL (childLL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00113022 :
    adaptiveCoverCheck 11 (childHL (childHL (childLL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHL (childLL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childLL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00113023 :
    adaptiveCoverCheck 11 (childHH (childHL (childLL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHL (childLL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childLL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00113030 :
    adaptiveCoverCheck 11 (childLL (childHH (childLL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childHH (childLL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHH (childLL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00113031 :
    adaptiveCoverCheck 11 (childLH (childHH (childLL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childHH (childLL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHH (childLL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00113032 :
    adaptiveCoverCheck 11 (childHL (childHH (childLL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHH (childLL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childLL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00113033 :
    adaptiveCoverCheck 11 (childHH (childHH (childLL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHH (childLL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childLL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0011310 :
    adaptiveCoverCheck 12 (childLL (childLH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childLL (childLH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0011311 :
    adaptiveCoverCheck 12 (childLH (childLH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childLH (childLH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00113120 :
    adaptiveCoverCheck 11 (childLL (childHL (childLH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childHL (childLH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHL (childLH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00113121 :
    adaptiveCoverCheck 11 (childLH (childHL (childLH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childHL (childLH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHL (childLH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00113122 :
    adaptiveCoverCheck 11 (childHL (childHL (childLH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHL (childLH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childLH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00113123 :
    adaptiveCoverCheck 11 (childHH (childHL (childLH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHL (childLH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childLH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00113130 :
    adaptiveCoverCheck 11 (childLL (childHH (childLH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childHH (childLH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHH (childLH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00113131 :
    adaptiveCoverCheck 11 (childLH (childHH (childLH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childHH (childLH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHH (childLH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00113132 :
    adaptiveCoverCheck 11 (childHL (childHH (childLH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHH (childLH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childLH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00113133 :
    adaptiveCoverCheck 11 (childHH (childHH (childLH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHH (childLH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childLH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf001132000 :
    adaptiveCoverCheck 10 (childLL (childLL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf001132001 :
    adaptiveCoverCheck 10 (childLH (childLL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0011320020 :
    adaptiveCoverCheck 9 (childLL (childHL (childLL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childLL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childLL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0011320021 :
    adaptiveCoverCheck 9 (childLH (childHL (childLL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childLL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childLL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0011320030 :
    adaptiveCoverCheck 9 (childLL (childHH (childLL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childLL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childLL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0011320031 :
    adaptiveCoverCheck 9 (childLH (childHH (childLL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childLL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childLL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf001132010 :
    adaptiveCoverCheck 10 (childLL (childLH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf001132011 :
    adaptiveCoverCheck 10 (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0011320120 :
    adaptiveCoverCheck 9 (childLL (childHL (childLH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childLH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childLH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0011320121 :
    adaptiveCoverCheck 9 (childLH (childHL (childLH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childLH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childLH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0011320130 :
    adaptiveCoverCheck 9 (childLL (childHH (childLH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childLH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childLH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0011320131 :
    adaptiveCoverCheck 9 (childLH (childHH (childLH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childLH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childLH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0011320202 :
    adaptiveCoverCheck 9 (childHL (childLL (childHL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0011320203 :
    adaptiveCoverCheck 9 (childHH (childLL (childHL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0011320212 :
    adaptiveCoverCheck 9 (childHL (childLH (childHL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0011320213 :
    adaptiveCoverCheck 9 (childHH (childLH (childHL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf001132022 :
    adaptiveCoverCheck 10 (childHL (childHL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf001132023 :
    adaptiveCoverCheck 10 (childHH (childHL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0011320302 :
    adaptiveCoverCheck 9 (childHL (childLL (childHH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0011320303 :
    adaptiveCoverCheck 9 (childHH (childLL (childHH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0011320312 :
    adaptiveCoverCheck 9 (childHL (childLH (childHH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0011320313 :
    adaptiveCoverCheck 9 (childHH (childLH (childHH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf001132032 :
    adaptiveCoverCheck 10 (childHL (childHH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf001132033 :
    adaptiveCoverCheck 10 (childHH (childHH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf001132100 :
    adaptiveCoverCheck 10 (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf001132101 :
    adaptiveCoverCheck 10 (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0011321020 :
    adaptiveCoverCheck 9 (childLL (childHL (childLL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childLL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childLL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0011321021 :
    adaptiveCoverCheck 9 (childLH (childHL (childLL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childLL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childLL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0011321030 :
    adaptiveCoverCheck 9 (childLL (childHH (childLL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childLL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childLL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0011321031 :
    adaptiveCoverCheck 9 (childLH (childHH (childLL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childLL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childLL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf001132110 :
    adaptiveCoverCheck 10 (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf001132111 :
    adaptiveCoverCheck 10 (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0011321120 :
    adaptiveCoverCheck 9 (childLL (childHL (childLH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childLH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childLH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0011321121 :
    adaptiveCoverCheck 9 (childLH (childHL (childLH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childLH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childLH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0011321130 :
    adaptiveCoverCheck 9 (childLL (childHH (childLH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childLH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childLH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0011321131 :
    adaptiveCoverCheck 9 (childLH (childHH (childLH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childLH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childLH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0011321202 :
    adaptiveCoverCheck 9 (childHL (childLL (childHL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0011321203 :
    adaptiveCoverCheck 9 (childHH (childLL (childHL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0011321212 :
    adaptiveCoverCheck 9 (childHL (childLH (childHL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0011321213 :
    adaptiveCoverCheck 9 (childHH (childLH (childHL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf001132122 :
    adaptiveCoverCheck 10 (childHL (childHL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf001132123 :
    adaptiveCoverCheck 10 (childHH (childHL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0011321302 :
    adaptiveCoverCheck 9 (childHL (childLL (childHH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0011321303 :
    adaptiveCoverCheck 9 (childHH (childLL (childHH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0011321312 :
    adaptiveCoverCheck 9 (childHL (childLH (childHH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0011321313 :
    adaptiveCoverCheck 9 (childHH (childLH (childHH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf001132132 :
    adaptiveCoverCheck 10 (childHL (childHH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf001132133 :
    adaptiveCoverCheck 10 (childHH (childHH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00113220 :
    adaptiveCoverCheck 11 (childLL (childHL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childHL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00113221 :
    adaptiveCoverCheck 11 (childLH (childHL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childHL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00113222 :
    adaptiveCoverCheck 11 (childHL (childHL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00113223 :
    adaptiveCoverCheck 11 (childHH (childHL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00113230 :
    adaptiveCoverCheck 11 (childLL (childHH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childHH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00113231 :
    adaptiveCoverCheck 11 (childLH (childHH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childHH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00113232 :
    adaptiveCoverCheck 11 (childHL (childHH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00113233 :
    adaptiveCoverCheck 11 (childHH (childHH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf001133000 :
    adaptiveCoverCheck 10 (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf001133001 :
    adaptiveCoverCheck 10 (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0011330020 :
    adaptiveCoverCheck 9 (childLL (childHL (childLL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childLL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childLL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0011330021 :
    adaptiveCoverCheck 9 (childLH (childHL (childLL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childLL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childLL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0011330030 :
    adaptiveCoverCheck 9 (childLL (childHH (childLL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childLL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childLL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0011330031 :
    adaptiveCoverCheck 9 (childLH (childHH (childLL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childLL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childLL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf001133010 :
    adaptiveCoverCheck 10 (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf001133011 :
    adaptiveCoverCheck 10 (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0011330120 :
    adaptiveCoverCheck 9 (childLL (childHL (childLH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childLH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childLH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0011330121 :
    adaptiveCoverCheck 9 (childLH (childHL (childLH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childLH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childLH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0011330130 :
    adaptiveCoverCheck 9 (childLL (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0011330131 :
    adaptiveCoverCheck 9 (childLH (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0011330202 :
    adaptiveCoverCheck 9 (childHL (childLL (childHL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0011330203 :
    adaptiveCoverCheck 9 (childHH (childLL (childHL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0011330212 :
    adaptiveCoverCheck 9 (childHL (childLH (childHL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0011330213 :
    adaptiveCoverCheck 9 (childHH (childLH (childHL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf001133022 :
    adaptiveCoverCheck 10 (childHL (childHL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf001133023 :
    adaptiveCoverCheck 10 (childHH (childHL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0011330302 :
    adaptiveCoverCheck 9 (childHL (childLL (childHH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0011330303 :
    adaptiveCoverCheck 9 (childHH (childLL (childHH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0011330312 :
    adaptiveCoverCheck 9 (childHL (childLH (childHH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0011330313 :
    adaptiveCoverCheck 9 (childHH (childLH (childHH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf001133032 :
    adaptiveCoverCheck 10 (childHL (childHH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf001133033 :
    adaptiveCoverCheck 10 (childHH (childHH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf001133100 :
    adaptiveCoverCheck 10 (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf001133101 :
    adaptiveCoverCheck 10 (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0011331020 :
    adaptiveCoverCheck 9 (childLL (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0011331021 :
    adaptiveCoverCheck 9 (childLH (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0011331030 :
    adaptiveCoverCheck 9 (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0011331031 :
    adaptiveCoverCheck 9 (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf001133110 :
    adaptiveCoverCheck 10 (childLL (childLH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf001133111 :
    adaptiveCoverCheck 10 (childLH (childLH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0011331120 :
    adaptiveCoverCheck 9 (childLL (childHL (childLH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childLH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childLH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0011331121 :
    adaptiveCoverCheck 9 (childLH (childHL (childLH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childLH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childLH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0011331130 :
    adaptiveCoverCheck 9 (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0011331131 :
    adaptiveCoverCheck 9 (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0011331202 :
    adaptiveCoverCheck 9 (childHL (childLL (childHL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0011331203 :
    adaptiveCoverCheck 9 (childHH (childLL (childHL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0011331212 :
    adaptiveCoverCheck 9 (childHL (childLH (childHL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0011331213 :
    adaptiveCoverCheck 9 (childHH (childLH (childHL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf001133122 :
    adaptiveCoverCheck 10 (childHL (childHL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf001133123 :
    adaptiveCoverCheck 10 (childHH (childHL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0011331302 :
    adaptiveCoverCheck 9 (childHL (childLL (childHH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0011331303 :
    adaptiveCoverCheck 9 (childHH (childLL (childHH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0011331312 :
    adaptiveCoverCheck 9 (childHL (childLH (childHH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0011331313 :
    adaptiveCoverCheck 9 (childHH (childLH (childHH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf001133132 :
    adaptiveCoverCheck 10 (childHL (childHH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf001133133 :
    adaptiveCoverCheck 10 (childHH (childHH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childLH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00113320 :
    adaptiveCoverCheck 11 (childLL (childHL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childHL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00113321 :
    adaptiveCoverCheck 11 (childLH (childHL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childHL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00113322 :
    adaptiveCoverCheck 11 (childHL (childHL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00113323 :
    adaptiveCoverCheck 11 (childHH (childHL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00113330 :
    adaptiveCoverCheck 11 (childLL (childHH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childHH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00113331 :
    adaptiveCoverCheck 11 (childLH (childHH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childHH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00113332 :
    adaptiveCoverCheck 11 (childHL (childHH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00113333 :
    adaptiveCoverCheck 11 (childHH (childHH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0012000 :
    adaptiveCoverCheck 12 (childLL (childLL (childLL (childHL (childLH (childLL (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childLL (childLL (childLL (childHL (childLH (childLL (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childLL (childHL (childLH (childLL (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0012001 :
    adaptiveCoverCheck 12 (childLH (childLL (childLL (childHL (childLH (childLL (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childLH (childLL (childLL (childHL (childLH (childLL (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childLL (childHL (childLH (childLL (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0012002 :
    adaptiveCoverCheck 12 (childHL (childLL (childLL (childHL (childLH (childLL (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childHL (childLL (childLL (childHL (childLH (childLL (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL (childLL (childHL (childLH (childLL (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0012003 :
    adaptiveCoverCheck 12 (childHH (childLL (childLL (childHL (childLH (childLL (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childHH (childLL (childLL (childHL (childLH (childLL (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL (childLL (childHL (childLH (childLL (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0012010 :
    adaptiveCoverCheck 12 (childLL (childLH (childLL (childHL (childLH (childLL (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childLL (childLH (childLL (childHL (childLH (childLL (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childLL (childHL (childLH (childLL (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0012011 :
    adaptiveCoverCheck 12 (childLH (childLH (childLL (childHL (childLH (childLL (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childLH (childLH (childLL (childHL (childLH (childLL (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childLL (childHL (childLH (childLL (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0012012 :
    adaptiveCoverCheck 12 (childHL (childLH (childLL (childHL (childLH (childLL (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childHL (childLH (childLL (childHL (childLH (childLL (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childLL (childHL (childLH (childLL (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0012013 :
    adaptiveCoverCheck 12 (childHH (childLH (childLL (childHL (childLH (childLL (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childHH (childLH (childLL (childHL (childLH (childLL (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childLL (childHL (childLH (childLL (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf001202 :
    adaptiveCoverCheck 13 (childHL (childLL (childHL (childLH (childLL (childLL e24ThetaAboveRoot)))))) = true := by
  have h : ((childHL (childLL (childHL (childLH (childLL (childLL e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLL (childHL (childLH (childLL (childLL e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf001203 :
    adaptiveCoverCheck 13 (childHH (childLL (childHL (childLH (childLL (childLL e24ThetaAboveRoot)))))) = true := by
  have h : ((childHH (childLL (childHL (childLH (childLL (childLL e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLL (childHL (childLH (childLL (childLL e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0012100 :
    adaptiveCoverCheck 12 (childLL (childLL (childLH (childHL (childLH (childLL (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childLL (childLL (childLH (childHL (childLH (childLL (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childLH (childHL (childLH (childLL (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0012101 :
    adaptiveCoverCheck 12 (childLH (childLL (childLH (childHL (childLH (childLL (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childLH (childLL (childLH (childHL (childLH (childLL (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childLH (childHL (childLH (childLL (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0012102 :
    adaptiveCoverCheck 12 (childHL (childLL (childLH (childHL (childLH (childLL (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childHL (childLL (childLH (childHL (childLH (childLL (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL (childLH (childHL (childLH (childLL (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0012103 :
    adaptiveCoverCheck 12 (childHH (childLL (childLH (childHL (childLH (childLL (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childHH (childLL (childLH (childHL (childLH (childLL (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL (childLH (childHL (childLH (childLL (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0012110 :
    adaptiveCoverCheck 12 (childLL (childLH (childLH (childHL (childLH (childLL (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childLL (childLH (childLH (childHL (childLH (childLL (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childLH (childHL (childLH (childLL (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0012111 :
    adaptiveCoverCheck 12 (childLH (childLH (childLH (childHL (childLH (childLL (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childLH (childLH (childLH (childHL (childLH (childLL (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childLH (childHL (childLH (childLL (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0012112 :
    adaptiveCoverCheck 12 (childHL (childLH (childLH (childHL (childLH (childLL (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childHL (childLH (childLH (childHL (childLH (childLL (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childLH (childHL (childLH (childLL (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0012113 :
    adaptiveCoverCheck 12 (childHH (childLH (childLH (childHL (childLH (childLL (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childHH (childLH (childLH (childHL (childLH (childLL (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childLH (childHL (childLH (childLL (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf001212 :
    adaptiveCoverCheck 13 (childHL (childLH (childHL (childLH (childLL (childLL e24ThetaAboveRoot)))))) = true := by
  have h : ((childHL (childLH (childHL (childLH (childLL (childLL e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLH (childHL (childLH (childLL (childLL e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf001213 :
    adaptiveCoverCheck 13 (childHH (childLH (childHL (childLH (childLL (childLL e24ThetaAboveRoot)))))) = true := by
  have h : ((childHH (childLH (childHL (childLH (childLL (childLL e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLH (childHL (childLH (childLL (childLL e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00122 :
    adaptiveCoverCheck 14 (childHL (childHL (childLH (childLL (childLL e24ThetaAboveRoot))))) = true := by
  have h : ((childHL (childHL (childLH (childLL (childLL e24ThetaAboveRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 (childHL (childHL (childLH (childLL (childLL e24ThetaAboveRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00123 :
    adaptiveCoverCheck 14 (childHH (childHL (childLH (childLL (childLL e24ThetaAboveRoot))))) = true := by
  have h : ((childHH (childHL (childLH (childLL (childLL e24ThetaAboveRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 (childHH (childHL (childLH (childLL (childLL e24ThetaAboveRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0013000 :
    adaptiveCoverCheck 12 (childLL (childLL (childLL (childHH (childLH (childLL (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childLL (childLL (childLL (childHH (childLH (childLL (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childLL (childHH (childLH (childLL (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0013001 :
    adaptiveCoverCheck 12 (childLH (childLL (childLL (childHH (childLH (childLL (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childLH (childLL (childLL (childHH (childLH (childLL (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childLL (childHH (childLH (childLL (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0013002 :
    adaptiveCoverCheck 12 (childHL (childLL (childLL (childHH (childLH (childLL (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childHL (childLL (childLL (childHH (childLH (childLL (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL (childLL (childHH (childLH (childLL (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0013003 :
    adaptiveCoverCheck 12 (childHH (childLL (childLL (childHH (childLH (childLL (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childHH (childLL (childLL (childHH (childLH (childLL (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL (childLL (childHH (childLH (childLL (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0013010 :
    adaptiveCoverCheck 12 (childLL (childLH (childLL (childHH (childLH (childLL (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childLL (childLH (childLL (childHH (childLH (childLL (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childLL (childHH (childLH (childLL (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0013011 :
    adaptiveCoverCheck 12 (childLH (childLH (childLL (childHH (childLH (childLL (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childLH (childLH (childLL (childHH (childLH (childLL (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childLL (childHH (childLH (childLL (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0013012 :
    adaptiveCoverCheck 12 (childHL (childLH (childLL (childHH (childLH (childLL (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childHL (childLH (childLL (childHH (childLH (childLL (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childLL (childHH (childLH (childLL (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0013013 :
    adaptiveCoverCheck 12 (childHH (childLH (childLL (childHH (childLH (childLL (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childHH (childLH (childLL (childHH (childLH (childLL (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childLL (childHH (childLH (childLL (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf001302 :
    adaptiveCoverCheck 13 (childHL (childLL (childHH (childLH (childLL (childLL e24ThetaAboveRoot)))))) = true := by
  have h : ((childHL (childLL (childHH (childLH (childLL (childLL e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLL (childHH (childLH (childLL (childLL e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf001303 :
    adaptiveCoverCheck 13 (childHH (childLL (childHH (childLH (childLL (childLL e24ThetaAboveRoot)))))) = true := by
  have h : ((childHH (childLL (childHH (childLH (childLL (childLL e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLL (childHH (childLH (childLL (childLL e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0013100 :
    adaptiveCoverCheck 12 (childLL (childLL (childLH (childHH (childLH (childLL (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childLL (childLL (childLH (childHH (childLH (childLL (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childLH (childHH (childLH (childLL (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0013101 :
    adaptiveCoverCheck 12 (childLH (childLL (childLH (childHH (childLH (childLL (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childLH (childLL (childLH (childHH (childLH (childLL (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childLH (childHH (childLH (childLL (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0013102 :
    adaptiveCoverCheck 12 (childHL (childLL (childLH (childHH (childLH (childLL (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childHL (childLL (childLH (childHH (childLH (childLL (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL (childLH (childHH (childLH (childLL (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0013103 :
    adaptiveCoverCheck 12 (childHH (childLL (childLH (childHH (childLH (childLL (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childHH (childLL (childLH (childHH (childLH (childLL (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL (childLH (childHH (childLH (childLL (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0013110 :
    adaptiveCoverCheck 12 (childLL (childLH (childLH (childHH (childLH (childLL (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childLL (childLH (childLH (childHH (childLH (childLL (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childLH (childHH (childLH (childLL (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0013111 :
    adaptiveCoverCheck 12 (childLH (childLH (childLH (childHH (childLH (childLL (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childLH (childLH (childLH (childHH (childLH (childLL (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childLH (childHH (childLH (childLL (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0013112 :
    adaptiveCoverCheck 12 (childHL (childLH (childLH (childHH (childLH (childLL (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childHL (childLH (childLH (childHH (childLH (childLL (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childLH (childHH (childLH (childLL (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0013113 :
    adaptiveCoverCheck 12 (childHH (childLH (childLH (childHH (childLH (childLL (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childHH (childLH (childLH (childHH (childLH (childLL (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childLH (childHH (childLH (childLL (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf001312 :
    adaptiveCoverCheck 13 (childHL (childLH (childHH (childLH (childLL (childLL e24ThetaAboveRoot)))))) = true := by
  have h : ((childHL (childLH (childHH (childLH (childLL (childLL e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLH (childHH (childLH (childLL (childLL e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf001313 :
    adaptiveCoverCheck 13 (childHH (childLH (childHH (childLH (childLL (childLL e24ThetaAboveRoot)))))) = true := by
  have h : ((childHH (childLH (childHH (childLH (childLL (childLL e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLH (childHH (childLH (childLL (childLL e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00132 :
    adaptiveCoverCheck 14 (childHL (childHH (childLH (childLL (childLL e24ThetaAboveRoot))))) = true := by
  have h : ((childHL (childHH (childLH (childLL (childLL e24ThetaAboveRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 (childHL (childHH (childLH (childLL (childLL e24ThetaAboveRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00133 :
    adaptiveCoverCheck 14 (childHH (childHH (childLH (childLL (childLL e24ThetaAboveRoot))))) = true := by
  have h : ((childHH (childHH (childLH (childLL (childLL e24ThetaAboveRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 (childHH (childHH (childLH (childLL (childLL e24ThetaAboveRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0020 :
    adaptiveCoverCheck 15 (childLL (childHL (childLL (childLL e24ThetaAboveRoot)))) = true := by
  have h : ((childLL (childHL (childLL (childLL e24ThetaAboveRoot))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 (childLL (childHL (childLL (childLL e24ThetaAboveRoot)))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0021 :
    adaptiveCoverCheck 15 (childLH (childHL (childLL (childLL e24ThetaAboveRoot)))) = true := by
  have h : ((childLH (childHL (childLL (childLL e24ThetaAboveRoot))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 (childLH (childHL (childLL (childLL e24ThetaAboveRoot)))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0022 :
    adaptiveCoverCheck 15 (childHL (childHL (childLL (childLL e24ThetaAboveRoot)))) = true := by
  have h : ((childHL (childHL (childLL (childLL e24ThetaAboveRoot))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 (childHL (childHL (childLL (childLL e24ThetaAboveRoot)))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0023 :
    adaptiveCoverCheck 15 (childHH (childHL (childLL (childLL e24ThetaAboveRoot)))) = true := by
  have h : ((childHH (childHL (childLL (childLL e24ThetaAboveRoot))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 (childHH (childHL (childLL (childLL e24ThetaAboveRoot)))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0030 :
    adaptiveCoverCheck 15 (childLL (childHH (childLL (childLL e24ThetaAboveRoot)))) = true := by
  have h : ((childLL (childHH (childLL (childLL e24ThetaAboveRoot))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 (childLL (childHH (childLL (childLL e24ThetaAboveRoot)))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0031 :
    adaptiveCoverCheck 15 (childLH (childHH (childLL (childLL e24ThetaAboveRoot)))) = true := by
  have h : ((childLH (childHH (childLL (childLL e24ThetaAboveRoot))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 (childLH (childHH (childLL (childLL e24ThetaAboveRoot)))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0032 :
    adaptiveCoverCheck 15 (childHL (childHH (childLL (childLL e24ThetaAboveRoot)))) = true := by
  have h : ((childHL (childHH (childLL (childLL e24ThetaAboveRoot))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 (childHL (childHH (childLL (childLL e24ThetaAboveRoot)))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0033 :
    adaptiveCoverCheck 15 (childHH (childHH (childLL (childLL e24ThetaAboveRoot)))) = true := by
  have h : ((childHH (childHH (childLL (childLL e24ThetaAboveRoot))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 (childHH (childHH (childLL (childLL e24ThetaAboveRoot)))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010000 :
    adaptiveCoverCheck 13 (childLL (childLL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))) = true := by
  have h : ((childLL (childLL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL (childLL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010001 :
    adaptiveCoverCheck 13 (childLH (childLL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))) = true := by
  have h : ((childLH (childLL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH (childLL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010002 :
    adaptiveCoverCheck 13 (childHL (childLL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))) = true := by
  have h : ((childHL (childLL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010003 :
    adaptiveCoverCheck 13 (childHH (childLL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))) = true := by
  have h : ((childHH (childLL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010010 :
    adaptiveCoverCheck 13 (childLL (childLH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))) = true := by
  have h : ((childLL (childLH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL (childLH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010011 :
    adaptiveCoverCheck 13 (childLH (childLH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))) = true := by
  have h : ((childLH (childLH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH (childLH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010012 :
    adaptiveCoverCheck 13 (childHL (childLH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))) = true := by
  have h : ((childHL (childLH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010013 :
    adaptiveCoverCheck 13 (childHH (childLH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))) = true := by
  have h : ((childHH (childLH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100200 :
    adaptiveCoverCheck 12 (childLL (childLL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childLL (childLL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100201 :
    adaptiveCoverCheck 12 (childLH (childLL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childLH (childLL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01002020 :
    adaptiveCoverCheck 11 (childLL (childHL (childLL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childHL (childLL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHL (childLL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01002021 :
    adaptiveCoverCheck 11 (childLH (childHL (childLL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childHL (childLL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHL (childLL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01002022 :
    adaptiveCoverCheck 11 (childHL (childHL (childLL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHL (childLL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childLL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01002023 :
    adaptiveCoverCheck 11 (childHH (childHL (childLL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHL (childLL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childLL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01002030 :
    adaptiveCoverCheck 11 (childLL (childHH (childLL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childHH (childLL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHH (childLL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01002031 :
    adaptiveCoverCheck 11 (childLH (childHH (childLL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childHH (childLL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHH (childLL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01002032 :
    adaptiveCoverCheck 11 (childHL (childHH (childLL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHH (childLL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childLL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01002033 :
    adaptiveCoverCheck 11 (childHH (childHH (childLL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHH (childLL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childLL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100210 :
    adaptiveCoverCheck 12 (childLL (childLH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childLL (childLH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100211 :
    adaptiveCoverCheck 12 (childLH (childLH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childLH (childLH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01002120 :
    adaptiveCoverCheck 11 (childLL (childHL (childLH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childHL (childLH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHL (childLH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01002121 :
    adaptiveCoverCheck 11 (childLH (childHL (childLH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childHL (childLH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHL (childLH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01002122 :
    adaptiveCoverCheck 11 (childHL (childHL (childLH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHL (childLH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childLH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01002123 :
    adaptiveCoverCheck 11 (childHH (childHL (childLH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHL (childLH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childLH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01002130 :
    adaptiveCoverCheck 11 (childLL (childHH (childLH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childHH (childLH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHH (childLH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01002131 :
    adaptiveCoverCheck 11 (childLH (childHH (childLH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childHH (childLH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHH (childLH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01002132 :
    adaptiveCoverCheck 11 (childHL (childHH (childLH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHH (childLH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childLH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01002133 :
    adaptiveCoverCheck 11 (childHH (childHH (childLH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHH (childLH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childLH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010022000 :
    adaptiveCoverCheck 10 (childLL (childLL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010022001 :
    adaptiveCoverCheck 10 (childLH (childLL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100220020 :
    adaptiveCoverCheck 9 (childLL (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100220021 :
    adaptiveCoverCheck 9 (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100220030 :
    adaptiveCoverCheck 9 (childLL (childHH (childLL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childLL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childLL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100220031 :
    adaptiveCoverCheck 9 (childLH (childHH (childLL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childLL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childLL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010022010 :
    adaptiveCoverCheck 10 (childLL (childLH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010022011 :
    adaptiveCoverCheck 10 (childLH (childLH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100220120 :
    adaptiveCoverCheck 9 (childLL (childHL (childLH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childLH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childLH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100220121 :
    adaptiveCoverCheck 9 (childLH (childHL (childLH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childLH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childLH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100220130 :
    adaptiveCoverCheck 9 (childLL (childHH (childLH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childLH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childLH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100220131 :
    adaptiveCoverCheck 9 (childLH (childHH (childLH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childLH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childLH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100220202 :
    adaptiveCoverCheck 9 (childHL (childLL (childHL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100220203 :
    adaptiveCoverCheck 9 (childHH (childLL (childHL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010022022 :
    adaptiveCoverCheck 10 (childHL (childHL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010022023 :
    adaptiveCoverCheck 10 (childHH (childHL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010022032 :
    adaptiveCoverCheck 10 (childHL (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010022033 :
    adaptiveCoverCheck 10 (childHH (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010022100 :
    adaptiveCoverCheck 10 (childLL (childLL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010022101 :
    adaptiveCoverCheck 10 (childLH (childLL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100221020 :
    adaptiveCoverCheck 9 (childLL (childHL (childLL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childLL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childLL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100221021 :
    adaptiveCoverCheck 9 (childLH (childHL (childLL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childLL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childLL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100221030 :
    adaptiveCoverCheck 9 (childLL (childHH (childLL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childLL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childLL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100221031 :
    adaptiveCoverCheck 9 (childLH (childHH (childLL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childLL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childLL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010022110 :
    adaptiveCoverCheck 10 (childLL (childLH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010022111 :
    adaptiveCoverCheck 10 (childLH (childLH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100221120 :
    adaptiveCoverCheck 9 (childLL (childHL (childLH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childLH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childLH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100221121 :
    adaptiveCoverCheck 9 (childLH (childHL (childLH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childLH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childLH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100221130 :
    adaptiveCoverCheck 9 (childLL (childHH (childLH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childLH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childLH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100221131 :
    adaptiveCoverCheck 9 (childLH (childHH (childLH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childLH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childLH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100221203 :
    adaptiveCoverCheck 9 (childHH (childLL (childHL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100221212 :
    adaptiveCoverCheck 9 (childHL (childLH (childHL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100221213 :
    adaptiveCoverCheck 9 (childHH (childLH (childHL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010022122 :
    adaptiveCoverCheck 10 (childHL (childHL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010022123 :
    adaptiveCoverCheck 10 (childHH (childHL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100221302 :
    adaptiveCoverCheck 9 (childHL (childLL (childHH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100221303 :
    adaptiveCoverCheck 9 (childHH (childLL (childHH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100221312 :
    adaptiveCoverCheck 9 (childHL (childLH (childHH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100221313 :
    adaptiveCoverCheck 9 (childHH (childLH (childHH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010022132 :
    adaptiveCoverCheck 10 (childHL (childHH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010022133 :
    adaptiveCoverCheck 10 (childHH (childHH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childLH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01002220 :
    adaptiveCoverCheck 11 (childLL (childHL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childHL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01002221 :
    adaptiveCoverCheck 11 (childLH (childHL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childHL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01002222 :
    adaptiveCoverCheck 11 (childHL (childHL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01002223 :
    adaptiveCoverCheck 11 (childHH (childHL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01002230 :
    adaptiveCoverCheck 11 (childLL (childHH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childHH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01002231 :
    adaptiveCoverCheck 11 (childLH (childHH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childHH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01002232 :
    adaptiveCoverCheck 11 (childHL (childHH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01002233 :
    adaptiveCoverCheck 11 (childHH (childHH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childHL (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010023000 :
    adaptiveCoverCheck 10 (childLL (childLL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010023001 :
    adaptiveCoverCheck 10 (childLH (childLL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100230020 :
    adaptiveCoverCheck 9 (childLL (childHL (childLL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childLL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childLL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100230021 :
    adaptiveCoverCheck 9 (childLH (childHL (childLL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childLL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childLL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100230030 :
    adaptiveCoverCheck 9 (childLL (childHH (childLL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childLL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childLL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100230031 :
    adaptiveCoverCheck 9 (childLH (childHH (childLL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childLL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childLL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010023010 :
    adaptiveCoverCheck 10 (childLL (childLH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010023011 :
    adaptiveCoverCheck 10 (childLH (childLH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100230120 :
    adaptiveCoverCheck 9 (childLL (childHL (childLH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childLH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childLH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100230121 :
    adaptiveCoverCheck 9 (childLH (childHL (childLH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childLH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childLH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100230130 :
    adaptiveCoverCheck 9 (childLL (childHH (childLH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childLH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childLH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100230131 :
    adaptiveCoverCheck 9 (childLH (childHH (childLH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childLH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childLH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100230202 :
    adaptiveCoverCheck 9 (childHL (childLL (childHL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100230203 :
    adaptiveCoverCheck 9 (childHH (childLL (childHL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100230212 :
    adaptiveCoverCheck 9 (childHL (childLH (childHL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100230213 :
    adaptiveCoverCheck 9 (childHH (childLH (childHL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010023022 :
    adaptiveCoverCheck 10 (childHL (childHL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010023023 :
    adaptiveCoverCheck 10 (childHH (childHL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100230302 :
    adaptiveCoverCheck 9 (childHL (childLL (childHH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100230303 :
    adaptiveCoverCheck 9 (childHH (childLL (childHH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100230312 :
    adaptiveCoverCheck 9 (childHL (childLH (childHH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100230313 :
    adaptiveCoverCheck 9 (childHH (childLH (childHH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100230320 :
    adaptiveCoverCheck 9 (childLL (childHL (childHH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childHH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childHH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100230321 :
    adaptiveCoverCheck 9 (childLH (childHL (childHH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childHH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childHH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100230322 :
    adaptiveCoverCheck 9 (childHL (childHL (childHH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childHH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childHH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100230323 :
    adaptiveCoverCheck 9 (childHH (childHL (childHH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childHH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childHH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100230330 :
    adaptiveCoverCheck 9 (childLL (childHH (childHH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childHH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childHH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100230331 :
    adaptiveCoverCheck 9 (childLH (childHH (childHH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childHH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childHH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100230332 :
    adaptiveCoverCheck 9 (childHL (childHH (childHH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childHH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childHH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100230333 :
    adaptiveCoverCheck 9 (childHH (childHH (childHH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childHH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childHH (childLL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010023100 :
    adaptiveCoverCheck 10 (childLL (childLL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010023101 :
    adaptiveCoverCheck 10 (childLH (childLL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100231020 :
    adaptiveCoverCheck 9 (childLL (childHL (childLL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childLL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childLL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100231021 :
    adaptiveCoverCheck 9 (childLH (childHL (childLL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childLL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childLL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100231030 :
    adaptiveCoverCheck 9 (childLL (childHH (childLL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childLL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childLL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100231031 :
    adaptiveCoverCheck 9 (childLH (childHH (childLL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childLL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childLL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010023110 :
    adaptiveCoverCheck 10 (childLL (childLH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010023111 :
    adaptiveCoverCheck 10 (childLH (childLH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100231120 :
    adaptiveCoverCheck 9 (childLL (childHL (childLH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childLH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childLH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100231121 :
    adaptiveCoverCheck 9 (childLH (childHL (childLH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childLH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childLH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100231130 :
    adaptiveCoverCheck 9 (childLL (childHH (childLH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childLH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childLH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100231131 :
    adaptiveCoverCheck 9 (childLH (childHH (childLH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childLH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childLH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100231200 :
    adaptiveCoverCheck 9 (childLL (childLL (childHL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100231201 :
    adaptiveCoverCheck 9 (childLH (childLL (childHL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100231202 :
    adaptiveCoverCheck 9 (childHL (childLL (childHL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100231203 :
    adaptiveCoverCheck 9 (childHH (childLL (childHL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100231210 :
    adaptiveCoverCheck 9 (childLL (childLH (childHL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childHL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100231211 :
    adaptiveCoverCheck 9 (childLH (childLH (childHL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childHL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100231212 :
    adaptiveCoverCheck 9 (childHL (childLH (childHL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100231213 :
    adaptiveCoverCheck 9 (childHH (childLH (childHL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100231220 :
    adaptiveCoverCheck 9 (childLL (childHL (childHL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childHL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childHL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100231221 :
    adaptiveCoverCheck 9 (childLH (childHL (childHL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childHL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childHL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100231222 :
    adaptiveCoverCheck 9 (childHL (childHL (childHL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childHL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childHL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100231223 :
    adaptiveCoverCheck 9 (childHH (childHL (childHL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childHL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childHL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100231230 :
    adaptiveCoverCheck 9 (childLL (childHH (childHL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childHL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childHL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100231231 :
    adaptiveCoverCheck 9 (childLH (childHH (childHL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childHL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childHL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100231232 :
    adaptiveCoverCheck 9 (childHL (childHH (childHL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childHL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childHL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100231233 :
    adaptiveCoverCheck 9 (childHH (childHH (childHL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childHL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childHL (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100231300 :
    adaptiveCoverCheck 9 (childLL (childLL (childHH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100231301 :
    adaptiveCoverCheck 9 (childLH (childLL (childHH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100231302 :
    adaptiveCoverCheck 9 (childHL (childLL (childHH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100231303 :
    adaptiveCoverCheck 9 (childHH (childLL (childHH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100231310 :
    adaptiveCoverCheck 9 (childLL (childLH (childHH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childHH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100231311 :
    adaptiveCoverCheck 9 (childLH (childLH (childHH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childHH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100231312 :
    adaptiveCoverCheck 9 (childHL (childLH (childHH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100231313 :
    adaptiveCoverCheck 9 (childHH (childLH (childHH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100231320 :
    adaptiveCoverCheck 9 (childLL (childHL (childHH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childHH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childHH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100231321 :
    adaptiveCoverCheck 9 (childLH (childHL (childHH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childHH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childHH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100231322 :
    adaptiveCoverCheck 9 (childHL (childHL (childHH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childHH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childHH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100231323 :
    adaptiveCoverCheck 9 (childHH (childHL (childHH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childHH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childHH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100231330 :
    adaptiveCoverCheck 9 (childLL (childHH (childHH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childHH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childHH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100231331 :
    adaptiveCoverCheck 9 (childLH (childHH (childHH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childHH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childHH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100231332 :
    adaptiveCoverCheck 9 (childHL (childHH (childHH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childHH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childHH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100231333 :
    adaptiveCoverCheck 9 (childHH (childHH (childHH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childHH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childHH (childLH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01002320 :
    adaptiveCoverCheck 11 (childLL (childHL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childHL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01002321 :
    adaptiveCoverCheck 11 (childLH (childHL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childHL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01002322 :
    adaptiveCoverCheck 11 (childHL (childHL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01002323 :
    adaptiveCoverCheck 11 (childHH (childHL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01002330 :
    adaptiveCoverCheck 11 (childLL (childHH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childHH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01002331 :
    adaptiveCoverCheck 11 (childLH (childHH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childHH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01002332 :
    adaptiveCoverCheck 11 (childHL (childHH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01002333 :
    adaptiveCoverCheck 11 (childHH (childHH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childHH (childHL (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100300 :
    adaptiveCoverCheck 12 (childLL (childLL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childLL (childLL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100301 :
    adaptiveCoverCheck 12 (childLH (childLL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childLH (childLL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01003020 :
    adaptiveCoverCheck 11 (childLL (childHL (childLL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childHL (childLL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHL (childLL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01003021 :
    adaptiveCoverCheck 11 (childLH (childHL (childLL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childHL (childLL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHL (childLL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01003022 :
    adaptiveCoverCheck 11 (childHL (childHL (childLL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHL (childLL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childLL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01003023 :
    adaptiveCoverCheck 11 (childHH (childHL (childLL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHL (childLL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childLL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01003030 :
    adaptiveCoverCheck 11 (childLL (childHH (childLL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childHH (childLL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHH (childLL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01003031 :
    adaptiveCoverCheck 11 (childLH (childHH (childLL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childHH (childLL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHH (childLL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01003032 :
    adaptiveCoverCheck 11 (childHL (childHH (childLL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHH (childLL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childLL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01003033 :
    adaptiveCoverCheck 11 (childHH (childHH (childLL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHH (childLL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childLL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100310 :
    adaptiveCoverCheck 12 (childLL (childLH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childLL (childLH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100311 :
    adaptiveCoverCheck 12 (childLH (childLH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childLH (childLH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01003120 :
    adaptiveCoverCheck 11 (childLL (childHL (childLH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childHL (childLH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHL (childLH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01003121 :
    adaptiveCoverCheck 11 (childLH (childHL (childLH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childHL (childLH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHL (childLH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01003122 :
    adaptiveCoverCheck 11 (childHL (childHL (childLH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHL (childLH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childLH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01003123 :
    adaptiveCoverCheck 11 (childHH (childHL (childLH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHL (childLH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childLH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01003130 :
    adaptiveCoverCheck 11 (childLL (childHH (childLH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childHH (childLH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHH (childLH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01003131 :
    adaptiveCoverCheck 11 (childLH (childHH (childLH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childHH (childLH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHH (childLH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01003132 :
    adaptiveCoverCheck 11 (childHL (childHH (childLH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHH (childLH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childLH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01003133 :
    adaptiveCoverCheck 11 (childHH (childHH (childLH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHH (childLH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childLH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010032000 :
    adaptiveCoverCheck 10 (childLL (childLL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010032001 :
    adaptiveCoverCheck 10 (childLH (childLL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100320020 :
    adaptiveCoverCheck 9 (childLL (childHL (childLL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childLL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childLL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100320021 :
    adaptiveCoverCheck 9 (childLH (childHL (childLL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childLL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childLL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100320030 :
    adaptiveCoverCheck 9 (childLL (childHH (childLL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childLL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childLL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100320031 :
    adaptiveCoverCheck 9 (childLH (childHH (childLL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childLL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childLL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010032010 :
    adaptiveCoverCheck 10 (childLL (childLH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010032011 :
    adaptiveCoverCheck 10 (childLH (childLH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100320120 :
    adaptiveCoverCheck 9 (childLL (childHL (childLH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childLH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childLH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100320121 :
    adaptiveCoverCheck 9 (childLH (childHL (childLH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childLH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childLH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100320130 :
    adaptiveCoverCheck 9 (childLL (childHH (childLH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childLH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childLH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100320131 :
    adaptiveCoverCheck 9 (childLH (childHH (childLH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childLH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childLH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100320200 :
    adaptiveCoverCheck 9 (childLL (childLL (childHL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100320201 :
    adaptiveCoverCheck 9 (childLH (childLL (childHL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100320202 :
    adaptiveCoverCheck 9 (childHL (childLL (childHL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100320203 :
    adaptiveCoverCheck 9 (childHH (childLL (childHL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100320210 :
    adaptiveCoverCheck 9 (childLL (childLH (childHL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childHL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100320211 :
    adaptiveCoverCheck 9 (childLH (childLH (childHL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childHL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100320212 :
    adaptiveCoverCheck 9 (childHL (childLH (childHL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100320213 :
    adaptiveCoverCheck 9 (childHH (childLH (childHL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100320220 :
    adaptiveCoverCheck 9 (childLL (childHL (childHL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childHL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childHL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100320221 :
    adaptiveCoverCheck 9 (childLH (childHL (childHL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childHL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childHL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100320222 :
    adaptiveCoverCheck 9 (childHL (childHL (childHL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childHL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childHL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100320223 :
    adaptiveCoverCheck 9 (childHH (childHL (childHL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childHL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childHL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100320230 :
    adaptiveCoverCheck 9 (childLL (childHH (childHL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childHL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childHL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100320231 :
    adaptiveCoverCheck 9 (childLH (childHH (childHL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childHL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childHL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100320232 :
    adaptiveCoverCheck 9 (childHL (childHH (childHL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childHL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childHL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100320233 :
    adaptiveCoverCheck 9 (childHH (childHH (childHL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childHL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childHL (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100320300 :
    adaptiveCoverCheck 9 (childLL (childLL (childHH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100320301 :
    adaptiveCoverCheck 9 (childLH (childLL (childHH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100320302 :
    adaptiveCoverCheck 9 (childHL (childLL (childHH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100320303 :
    adaptiveCoverCheck 9 (childHH (childLL (childHH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100320310 :
    adaptiveCoverCheck 9 (childLL (childLH (childHH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childHH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100320311 :
    adaptiveCoverCheck 9 (childLH (childLH (childHH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childHH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100320312 :
    adaptiveCoverCheck 9 (childHL (childLH (childHH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100320313 :
    adaptiveCoverCheck 9 (childHH (childLH (childHH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100320320 :
    adaptiveCoverCheck 9 (childLL (childHL (childHH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childHH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childHH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100320321 :
    adaptiveCoverCheck 9 (childLH (childHL (childHH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childHH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childHH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100320322 :
    adaptiveCoverCheck 9 (childHL (childHL (childHH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childHH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childHH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100320323 :
    adaptiveCoverCheck 9 (childHH (childHL (childHH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childHH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childHH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100320330 :
    adaptiveCoverCheck 9 (childLL (childHH (childHH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childHH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childHH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100320331 :
    adaptiveCoverCheck 9 (childLH (childHH (childHH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childHH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childHH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100320332 :
    adaptiveCoverCheck 9 (childHL (childHH (childHH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childHH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childHH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100320333 :
    adaptiveCoverCheck 9 (childHH (childHH (childHH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childHH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childHH (childLL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010032100 :
    adaptiveCoverCheck 10 (childLL (childLL (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010032101 :
    adaptiveCoverCheck 10 (childLH (childLL (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100321020 :
    adaptiveCoverCheck 9 (childLL (childHL (childLL (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childLL (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childLL (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100321021 :
    adaptiveCoverCheck 9 (childLH (childHL (childLL (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childLL (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childLL (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100321022 :
    adaptiveCoverCheck 9 (childHL (childHL (childLL (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childLL (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childLL (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100321023 :
    adaptiveCoverCheck 9 (childHH (childHL (childLL (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childLL (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childLL (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100321030 :
    adaptiveCoverCheck 9 (childLL (childHH (childLL (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childLL (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childLL (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100321031 :
    adaptiveCoverCheck 9 (childLH (childHH (childLL (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childLL (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childLL (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100321032 :
    adaptiveCoverCheck 9 (childHL (childHH (childLL (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childLL (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childLL (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100321033 :
    adaptiveCoverCheck 9 (childHH (childHH (childLL (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childLL (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childLL (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010032110 :
    adaptiveCoverCheck 10 (childLL (childLH (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010032111 :
    adaptiveCoverCheck 10 (childLH (childLH (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100321120 :
    adaptiveCoverCheck 9 (childLL (childHL (childLH (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childLH (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childLH (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100321121 :
    adaptiveCoverCheck 9 (childLH (childHL (childLH (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childLH (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childLH (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100321122 :
    adaptiveCoverCheck 9 (childHL (childHL (childLH (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childLH (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childLH (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100321123 :
    adaptiveCoverCheck 9 (childHH (childHL (childLH (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childLH (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childLH (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100321130 :
    adaptiveCoverCheck 9 (childLL (childHH (childLH (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childLH (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childLH (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100321131 :
    adaptiveCoverCheck 9 (childLH (childHH (childLH (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childLH (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childLH (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100321132 :
    adaptiveCoverCheck 9 (childHL (childHH (childLH (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childLH (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childLH (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100321133 :
    adaptiveCoverCheck 9 (childHH (childHH (childLH (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childLH (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childLH (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100321200 :
    adaptiveCoverCheck 9 (childLL (childLL (childHL (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHL (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHL (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100321201 :
    adaptiveCoverCheck 9 (childLH (childLL (childHL (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHL (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHL (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100321202 :
    adaptiveCoverCheck 9 (childHL (childLL (childHL (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHL (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHL (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100321203 :
    adaptiveCoverCheck 9 (childHH (childLL (childHL (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHL (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHL (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100321210 :
    adaptiveCoverCheck 9 (childLL (childLH (childHL (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childHL (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHL (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100321211 :
    adaptiveCoverCheck 9 (childLH (childLH (childHL (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childHL (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHL (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100321212 :
    adaptiveCoverCheck 9 (childHL (childLH (childHL (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHL (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHL (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100321213 :
    adaptiveCoverCheck 9 (childHH (childLH (childHL (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHL (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHL (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100321220 :
    adaptiveCoverCheck 9 (childLL (childHL (childHL (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childHL (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childHL (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100321221 :
    adaptiveCoverCheck 9 (childLH (childHL (childHL (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childHL (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childHL (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100321222 :
    adaptiveCoverCheck 9 (childHL (childHL (childHL (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childHL (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childHL (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100321223 :
    adaptiveCoverCheck 9 (childHH (childHL (childHL (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childHL (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childHL (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100321230 :
    adaptiveCoverCheck 9 (childLL (childHH (childHL (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childHL (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childHL (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100321231 :
    adaptiveCoverCheck 9 (childLH (childHH (childHL (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childHL (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childHL (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100321232 :
    adaptiveCoverCheck 9 (childHL (childHH (childHL (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childHL (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childHL (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100321233 :
    adaptiveCoverCheck 9 (childHH (childHH (childHL (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childHL (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childHL (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100321300 :
    adaptiveCoverCheck 9 (childLL (childLL (childHH (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHH (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHH (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100321301 :
    adaptiveCoverCheck 9 (childLH (childLL (childHH (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHH (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHH (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100321302 :
    adaptiveCoverCheck 9 (childHL (childLL (childHH (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHH (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHH (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100321303 :
    adaptiveCoverCheck 9 (childHH (childLL (childHH (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHH (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHH (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100321310 :
    adaptiveCoverCheck 9 (childLL (childLH (childHH (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childHH (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHH (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100321311 :
    adaptiveCoverCheck 9 (childLH (childLH (childHH (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childHH (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHH (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100321312 :
    adaptiveCoverCheck 9 (childHL (childLH (childHH (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHH (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHH (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100321313 :
    adaptiveCoverCheck 9 (childHH (childLH (childHH (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHH (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHH (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100321320 :
    adaptiveCoverCheck 9 (childLL (childHL (childHH (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childHH (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childHH (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100321321 :
    adaptiveCoverCheck 9 (childLH (childHL (childHH (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childHH (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childHH (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100321322 :
    adaptiveCoverCheck 9 (childHL (childHL (childHH (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childHH (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childHH (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100321323 :
    adaptiveCoverCheck 9 (childHH (childHL (childHH (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childHH (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childHH (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100321330 :
    adaptiveCoverCheck 9 (childLL (childHH (childHH (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childHH (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childHH (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100321331 :
    adaptiveCoverCheck 9 (childLH (childHH (childHH (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childHH (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childHH (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100321332 :
    adaptiveCoverCheck 9 (childHL (childHH (childHH (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childHH (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childHH (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100321333 :
    adaptiveCoverCheck 9 (childHH (childHH (childHH (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childHH (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childHH (childLH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01003220 :
    adaptiveCoverCheck 11 (childLL (childHL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childHL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01003221 :
    adaptiveCoverCheck 11 (childLH (childHL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childHL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01003222 :
    adaptiveCoverCheck 11 (childHL (childHL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01003223 :
    adaptiveCoverCheck 11 (childHH (childHL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01003230 :
    adaptiveCoverCheck 11 (childLL (childHH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childHH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01003231 :
    adaptiveCoverCheck 11 (childLH (childHH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childHH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01003232 :
    adaptiveCoverCheck 11 (childHL (childHH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01003233 :
    adaptiveCoverCheck 11 (childHH (childHH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childHL (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010033000 :
    adaptiveCoverCheck 10 (childLL (childLL (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010033001 :
    adaptiveCoverCheck 10 (childLH (childLL (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100330020 :
    adaptiveCoverCheck 9 (childLL (childHL (childLL (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childLL (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childLL (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100330021 :
    adaptiveCoverCheck 9 (childLH (childHL (childLL (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childLL (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childLL (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100330022 :
    adaptiveCoverCheck 9 (childHL (childHL (childLL (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childLL (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childLL (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100330023 :
    adaptiveCoverCheck 9 (childHH (childHL (childLL (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childLL (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childLL (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100330030 :
    adaptiveCoverCheck 9 (childLL (childHH (childLL (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childLL (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childLL (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100330031 :
    adaptiveCoverCheck 9 (childLH (childHH (childLL (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childLL (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childLL (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100330032 :
    adaptiveCoverCheck 9 (childHL (childHH (childLL (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childLL (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childLL (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100330033 :
    adaptiveCoverCheck 9 (childHH (childHH (childLL (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childLL (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childLL (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010033010 :
    adaptiveCoverCheck 10 (childLL (childLH (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010033011 :
    adaptiveCoverCheck 10 (childLH (childLH (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100330120 :
    adaptiveCoverCheck 9 (childLL (childHL (childLH (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childLH (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childLH (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100330121 :
    adaptiveCoverCheck 9 (childLH (childHL (childLH (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childLH (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childLH (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100330122 :
    adaptiveCoverCheck 9 (childHL (childHL (childLH (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childLH (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childLH (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100330123 :
    adaptiveCoverCheck 9 (childHH (childHL (childLH (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childLH (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childLH (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100330130 :
    adaptiveCoverCheck 9 (childLL (childHH (childLH (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childLH (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childLH (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100330131 :
    adaptiveCoverCheck 9 (childLH (childHH (childLH (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childLH (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childLH (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100330132 :
    adaptiveCoverCheck 9 (childHL (childHH (childLH (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childLH (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childLH (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100330133 :
    adaptiveCoverCheck 9 (childHH (childHH (childLH (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childLH (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childLH (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100330200 :
    adaptiveCoverCheck 9 (childLL (childLL (childHL (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHL (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHL (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100330201 :
    adaptiveCoverCheck 9 (childLH (childLL (childHL (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHL (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHL (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100330202 :
    adaptiveCoverCheck 9 (childHL (childLL (childHL (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHL (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHL (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100330203 :
    adaptiveCoverCheck 9 (childHH (childLL (childHL (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHL (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHL (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100330210 :
    adaptiveCoverCheck 9 (childLL (childLH (childHL (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childHL (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHL (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100330211 :
    adaptiveCoverCheck 9 (childLH (childLH (childHL (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childHL (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHL (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100330212 :
    adaptiveCoverCheck 9 (childHL (childLH (childHL (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHL (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHL (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100330213 :
    adaptiveCoverCheck 9 (childHH (childLH (childHL (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHL (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHL (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100330220 :
    adaptiveCoverCheck 9 (childLL (childHL (childHL (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childHL (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childHL (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100330221 :
    adaptiveCoverCheck 9 (childLH (childHL (childHL (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childHL (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childHL (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100330222 :
    adaptiveCoverCheck 9 (childHL (childHL (childHL (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childHL (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childHL (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100330223 :
    adaptiveCoverCheck 9 (childHH (childHL (childHL (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childHL (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childHL (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100330230 :
    adaptiveCoverCheck 9 (childLL (childHH (childHL (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childHL (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childHL (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100330231 :
    adaptiveCoverCheck 9 (childLH (childHH (childHL (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childHL (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childHL (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100330232 :
    adaptiveCoverCheck 9 (childHL (childHH (childHL (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childHL (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childHL (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0100330233 :
    adaptiveCoverCheck 9 (childHH (childHH (childHL (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childHL (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childHL (childLL (childHH (childHH (childLL (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

end PartE
end GerverSofa
