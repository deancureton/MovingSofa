import GerverSofa.KernelOnly.PartE.E24KC2ProofHelpers

/-! E24KC5 checkpoint-aware kernel batch. -/
noncomputable section

namespace GerverSofa
namespace PartE

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101033002 :
    adaptiveCoverCheck 10 (childHL (childLL (childLL (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLL (childLL (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childLL (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101033003 :
    adaptiveCoverCheck 10 (childHH (childLL (childLL (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLL (childLL (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childLL (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101033010 :
    adaptiveCoverCheck 10 (childLL (childLH (childLL (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childLL (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childLL (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101033011 :
    adaptiveCoverCheck 10 (childLH (childLH (childLL (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childLL (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childLL (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101033012 :
    adaptiveCoverCheck 10 (childHL (childLH (childLL (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLH (childLL (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childLL (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101033013 :
    adaptiveCoverCheck 10 (childHH (childLH (childLL (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLH (childLL (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childLL (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1010330200 :
    adaptiveCoverCheck 9 (childLL (childLL (childHL (childLL (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHL (childLL (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHL (childLL (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1010330201 :
    adaptiveCoverCheck 9 (childLH (childLL (childHL (childLL (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHL (childLL (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHL (childLL (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1010330202 :
    adaptiveCoverCheck 9 (childHL (childLL (childHL (childLL (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHL (childLL (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHL (childLL (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1010330203 :
    adaptiveCoverCheck 9 (childHH (childLL (childHL (childLL (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHL (childLL (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHL (childLL (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101033021 :
    adaptiveCoverCheck 10 (childLH (childHL (childLL (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHL (childLL (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHL (childLL (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101033022 :
    adaptiveCoverCheck 10 (childHL (childHL (childLL (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHL (childLL (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childLL (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101033023 :
    adaptiveCoverCheck 10 (childHH (childHL (childLL (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHL (childLL (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childLL (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101033030 :
    adaptiveCoverCheck 10 (childLL (childHH (childLL (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHH (childLL (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHH (childLL (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101033031 :
    adaptiveCoverCheck 10 (childLH (childHH (childLL (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHH (childLL (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHH (childLL (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101033032 :
    adaptiveCoverCheck 10 (childHL (childHH (childLL (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHH (childLL (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childLL (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101033033 :
    adaptiveCoverCheck 10 (childHH (childHH (childLL (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHH (childLL (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childLL (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101033100 :
    adaptiveCoverCheck 10 (childLL (childLL (childLH (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childLH (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childLH (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101033101 :
    adaptiveCoverCheck 10 (childLH (childLL (childLH (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childLH (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childLH (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101033102 :
    adaptiveCoverCheck 10 (childHL (childLL (childLH (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLL (childLH (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childLH (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101033103 :
    adaptiveCoverCheck 10 (childHH (childLL (childLH (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLL (childLH (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childLH (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101033110 :
    adaptiveCoverCheck 10 (childLL (childLH (childLH (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childLH (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childLH (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101033111 :
    adaptiveCoverCheck 10 (childLH (childLH (childLH (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childLH (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childLH (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101033112 :
    adaptiveCoverCheck 10 (childHL (childLH (childLH (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLH (childLH (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childLH (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101033113 :
    adaptiveCoverCheck 10 (childHH (childLH (childLH (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLH (childLH (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childLH (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101033120 :
    adaptiveCoverCheck 10 (childLL (childHL (childLH (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHL (childLH (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHL (childLH (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101033121 :
    adaptiveCoverCheck 10 (childLH (childHL (childLH (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHL (childLH (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHL (childLH (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101033122 :
    adaptiveCoverCheck 10 (childHL (childHL (childLH (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHL (childLH (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childLH (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101033123 :
    adaptiveCoverCheck 10 (childHH (childHL (childLH (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHL (childLH (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childLH (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101033130 :
    adaptiveCoverCheck 10 (childLL (childHH (childLH (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHH (childLH (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHH (childLH (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101033131 :
    adaptiveCoverCheck 10 (childLH (childHH (childLH (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHH (childLH (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHH (childLH (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101033132 :
    adaptiveCoverCheck 10 (childHL (childHH (childLH (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHH (childLH (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childLH (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101033133 :
    adaptiveCoverCheck 10 (childHH (childHH (childLH (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHH (childLH (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childLH (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101033200 :
    adaptiveCoverCheck 10 (childLL (childLL (childHL (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childHL (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childHL (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101033201 :
    adaptiveCoverCheck 10 (childLH (childLL (childHL (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childHL (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childHL (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101033202 :
    adaptiveCoverCheck 10 (childHL (childLL (childHL (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLL (childHL (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childHL (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101033203 :
    adaptiveCoverCheck 10 (childHH (childLL (childHL (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLL (childHL (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childHL (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101033210 :
    adaptiveCoverCheck 10 (childLL (childLH (childHL (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childHL (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childHL (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101033211 :
    adaptiveCoverCheck 10 (childLH (childLH (childHL (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childHL (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childHL (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101033212 :
    adaptiveCoverCheck 10 (childHL (childLH (childHL (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLH (childHL (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childHL (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101033213 :
    adaptiveCoverCheck 10 (childHH (childLH (childHL (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLH (childHL (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childHL (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf10103322 :
    adaptiveCoverCheck 11 (childHL (childHL (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHL (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf10103323 :
    adaptiveCoverCheck 11 (childHH (childHL (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHL (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101033300 :
    adaptiveCoverCheck 10 (childLL (childLL (childHH (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childHH (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childHH (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101033301 :
    adaptiveCoverCheck 10 (childLH (childLL (childHH (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childHH (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childHH (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101033302 :
    adaptiveCoverCheck 10 (childHL (childLL (childHH (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLL (childHH (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childHH (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101033303 :
    adaptiveCoverCheck 10 (childHH (childLL (childHH (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLL (childHH (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childHH (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101033310 :
    adaptiveCoverCheck 10 (childLL (childLH (childHH (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childHH (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childHH (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101033311 :
    adaptiveCoverCheck 10 (childLH (childLH (childHH (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childHH (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childHH (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101033312 :
    adaptiveCoverCheck 10 (childHL (childLH (childHH (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLH (childHH (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childHH (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101033313 :
    adaptiveCoverCheck 10 (childHH (childLH (childHH (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLH (childHH (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childHH (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf10103332 :
    adaptiveCoverCheck 11 (childHL (childHH (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHH (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf10103333 :
    adaptiveCoverCheck 11 (childHH (childHH (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHH (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101100 :
    adaptiveCoverCheck 13 (childLL (childLL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))) = true := by
  have h : ((childLL (childLL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL (childLL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101101 :
    adaptiveCoverCheck 13 (childLH (childLL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))) = true := by
  have h : ((childLH (childLL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH (childLL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101102 :
    adaptiveCoverCheck 13 (childHL (childLL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))) = true := by
  have h : ((childHL (childLL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101103 :
    adaptiveCoverCheck 13 (childHH (childLL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))) = true := by
  have h : ((childHH (childLL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101110 :
    adaptiveCoverCheck 13 (childLL (childLH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))) = true := by
  have h : ((childLL (childLH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL (childLH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101111 :
    adaptiveCoverCheck 13 (childLH (childLH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))) = true := by
  have h : ((childLH (childLH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH (childLH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101112 :
    adaptiveCoverCheck 13 (childHL (childLH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))) = true := by
  have h : ((childHL (childLH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101113 :
    adaptiveCoverCheck 13 (childHH (childLH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))) = true := by
  have h : ((childHH (childLH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1011200 :
    adaptiveCoverCheck 12 (childLL (childLL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLL (childLL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1011201 :
    adaptiveCoverCheck 12 (childLH (childLL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLH (childLL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1011202 :
    adaptiveCoverCheck 12 (childHL (childLL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childHL (childLL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1011203 :
    adaptiveCoverCheck 12 (childHH (childLL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childHH (childLL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1011210 :
    adaptiveCoverCheck 12 (childLL (childLH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLL (childLH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1011211 :
    adaptiveCoverCheck 12 (childLH (childLH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLH (childLH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1011212 :
    adaptiveCoverCheck 12 (childHL (childLH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childHL (childLH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1011213 :
    adaptiveCoverCheck 12 (childHH (childLH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childHH (childLH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101122000 :
    adaptiveCoverCheck 10 (childLL (childLL (childLL (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childLL (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childLL (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101122001 :
    adaptiveCoverCheck 10 (childLH (childLL (childLL (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childLL (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childLL (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101122002 :
    adaptiveCoverCheck 10 (childHL (childLL (childLL (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLL (childLL (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childLL (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101122003 :
    adaptiveCoverCheck 10 (childHH (childLL (childLL (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLL (childLL (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childLL (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101122010 :
    adaptiveCoverCheck 10 (childLL (childLH (childLL (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childLL (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childLL (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101122011 :
    adaptiveCoverCheck 10 (childLH (childLH (childLL (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childLL (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childLL (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101122012 :
    adaptiveCoverCheck 10 (childHL (childLH (childLL (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLH (childLL (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childLL (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101122013 :
    adaptiveCoverCheck 10 (childHH (childLH (childLL (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLH (childLL (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childLL (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101122020 :
    adaptiveCoverCheck 10 (childLL (childHL (childLL (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHL (childLL (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHL (childLL (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101122021 :
    adaptiveCoverCheck 10 (childLH (childHL (childLL (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHL (childLL (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHL (childLL (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101122022 :
    adaptiveCoverCheck 10 (childHL (childHL (childLL (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHL (childLL (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childLL (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101122023 :
    adaptiveCoverCheck 10 (childHH (childHL (childLL (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHL (childLL (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childLL (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101122030 :
    adaptiveCoverCheck 10 (childLL (childHH (childLL (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHH (childLL (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHH (childLL (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101122031 :
    adaptiveCoverCheck 10 (childLH (childHH (childLL (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHH (childLL (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHH (childLL (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101122032 :
    adaptiveCoverCheck 10 (childHL (childHH (childLL (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHH (childLL (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childLL (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101122033 :
    adaptiveCoverCheck 10 (childHH (childHH (childLL (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHH (childLL (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childLL (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101122100 :
    adaptiveCoverCheck 10 (childLL (childLL (childLH (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childLH (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childLH (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101122101 :
    adaptiveCoverCheck 10 (childLH (childLL (childLH (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childLH (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childLH (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101122102 :
    adaptiveCoverCheck 10 (childHL (childLL (childLH (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLL (childLH (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childLH (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101122103 :
    adaptiveCoverCheck 10 (childHH (childLL (childLH (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLL (childLH (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childLH (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101122110 :
    adaptiveCoverCheck 10 (childLL (childLH (childLH (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childLH (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childLH (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101122111 :
    adaptiveCoverCheck 10 (childLH (childLH (childLH (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childLH (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childLH (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101122112 :
    adaptiveCoverCheck 10 (childHL (childLH (childLH (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLH (childLH (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childLH (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101122113 :
    adaptiveCoverCheck 10 (childHH (childLH (childLH (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLH (childLH (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childLH (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101122120 :
    adaptiveCoverCheck 10 (childLL (childHL (childLH (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHL (childLH (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHL (childLH (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101122121 :
    adaptiveCoverCheck 10 (childLH (childHL (childLH (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHL (childLH (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHL (childLH (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101122122 :
    adaptiveCoverCheck 10 (childHL (childHL (childLH (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHL (childLH (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childLH (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101122123 :
    adaptiveCoverCheck 10 (childHH (childHL (childLH (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHL (childLH (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childLH (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101122130 :
    adaptiveCoverCheck 10 (childLL (childHH (childLH (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHH (childLH (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHH (childLH (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101122131 :
    adaptiveCoverCheck 10 (childLH (childHH (childLH (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHH (childLH (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHH (childLH (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101122132 :
    adaptiveCoverCheck 10 (childHL (childHH (childLH (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHH (childLH (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childLH (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101122133 :
    adaptiveCoverCheck 10 (childHH (childHH (childLH (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHH (childLH (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childLH (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101122200 :
    adaptiveCoverCheck 10 (childLL (childLL (childHL (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childHL (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childHL (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101122201 :
    adaptiveCoverCheck 10 (childLH (childLL (childHL (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childHL (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childHL (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101122202 :
    adaptiveCoverCheck 10 (childHL (childLL (childHL (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLL (childHL (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childHL (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101122203 :
    adaptiveCoverCheck 10 (childHH (childLL (childHL (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLL (childHL (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childHL (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101122210 :
    adaptiveCoverCheck 10 (childLL (childLH (childHL (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childHL (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childHL (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101122211 :
    adaptiveCoverCheck 10 (childLH (childLH (childHL (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childHL (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childHL (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101122212 :
    adaptiveCoverCheck 10 (childHL (childLH (childHL (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLH (childHL (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childHL (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101122213 :
    adaptiveCoverCheck 10 (childHH (childLH (childHL (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLH (childHL (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childHL (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf10112222 :
    adaptiveCoverCheck 11 (childHL (childHL (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHL (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf10112223 :
    adaptiveCoverCheck 11 (childHH (childHL (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHL (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101122300 :
    adaptiveCoverCheck 10 (childLL (childLL (childHH (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childHH (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childHH (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101122301 :
    adaptiveCoverCheck 10 (childLH (childLL (childHH (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childHH (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childHH (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101122302 :
    adaptiveCoverCheck 10 (childHL (childLL (childHH (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLL (childHH (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childHH (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101122303 :
    adaptiveCoverCheck 10 (childHH (childLL (childHH (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLL (childHH (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childHH (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101122310 :
    adaptiveCoverCheck 10 (childLL (childLH (childHH (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childHH (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childHH (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101122311 :
    adaptiveCoverCheck 10 (childLH (childLH (childHH (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childHH (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childHH (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101122312 :
    adaptiveCoverCheck 10 (childHL (childLH (childHH (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLH (childHH (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childHH (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101122313 :
    adaptiveCoverCheck 10 (childHH (childLH (childHH (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLH (childHH (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childHH (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf10112232 :
    adaptiveCoverCheck 11 (childHL (childHH (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHH (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf10112233 :
    adaptiveCoverCheck 11 (childHH (childHH (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHH (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101123000 :
    adaptiveCoverCheck 10 (childLL (childLL (childLL (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childLL (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childLL (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101123001 :
    adaptiveCoverCheck 10 (childLH (childLL (childLL (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childLL (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childLL (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101123002 :
    adaptiveCoverCheck 10 (childHL (childLL (childLL (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLL (childLL (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childLL (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101123003 :
    adaptiveCoverCheck 10 (childHH (childLL (childLL (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLL (childLL (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childLL (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101123010 :
    adaptiveCoverCheck 10 (childLL (childLH (childLL (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childLL (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childLL (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101123011 :
    adaptiveCoverCheck 10 (childLH (childLH (childLL (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childLL (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childLL (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101123012 :
    adaptiveCoverCheck 10 (childHL (childLH (childLL (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLH (childLL (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childLL (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101123013 :
    adaptiveCoverCheck 10 (childHH (childLH (childLL (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLH (childLL (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childLL (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101123020 :
    adaptiveCoverCheck 10 (childLL (childHL (childLL (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHL (childLL (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHL (childLL (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101123021 :
    adaptiveCoverCheck 10 (childLH (childHL (childLL (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHL (childLL (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHL (childLL (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101123022 :
    adaptiveCoverCheck 10 (childHL (childHL (childLL (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHL (childLL (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childLL (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101123023 :
    adaptiveCoverCheck 10 (childHH (childHL (childLL (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHL (childLL (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childLL (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101123030 :
    adaptiveCoverCheck 10 (childLL (childHH (childLL (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHH (childLL (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHH (childLL (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101123031 :
    adaptiveCoverCheck 10 (childLH (childHH (childLL (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHH (childLL (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHH (childLL (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101123032 :
    adaptiveCoverCheck 10 (childHL (childHH (childLL (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHH (childLL (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childLL (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101123033 :
    adaptiveCoverCheck 10 (childHH (childHH (childLL (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHH (childLL (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childLL (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101123100 :
    adaptiveCoverCheck 10 (childLL (childLL (childLH (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childLH (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childLH (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101123101 :
    adaptiveCoverCheck 10 (childLH (childLL (childLH (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childLH (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childLH (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101123102 :
    adaptiveCoverCheck 10 (childHL (childLL (childLH (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLL (childLH (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childLH (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101123103 :
    adaptiveCoverCheck 10 (childHH (childLL (childLH (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLL (childLH (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childLH (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101123110 :
    adaptiveCoverCheck 10 (childLL (childLH (childLH (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childLH (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childLH (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101123111 :
    adaptiveCoverCheck 10 (childLH (childLH (childLH (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childLH (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childLH (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101123112 :
    adaptiveCoverCheck 10 (childHL (childLH (childLH (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLH (childLH (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childLH (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101123113 :
    adaptiveCoverCheck 10 (childHH (childLH (childLH (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLH (childLH (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childLH (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101123120 :
    adaptiveCoverCheck 10 (childLL (childHL (childLH (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHL (childLH (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHL (childLH (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101123121 :
    adaptiveCoverCheck 10 (childLH (childHL (childLH (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHL (childLH (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHL (childLH (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101123122 :
    adaptiveCoverCheck 10 (childHL (childHL (childLH (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHL (childLH (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childLH (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101123123 :
    adaptiveCoverCheck 10 (childHH (childHL (childLH (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHL (childLH (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childLH (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101123130 :
    adaptiveCoverCheck 10 (childLL (childHH (childLH (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHH (childLH (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHH (childLH (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101123131 :
    adaptiveCoverCheck 10 (childLH (childHH (childLH (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHH (childLH (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHH (childLH (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101123132 :
    adaptiveCoverCheck 10 (childHL (childHH (childLH (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHH (childLH (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childLH (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101123133 :
    adaptiveCoverCheck 10 (childHH (childHH (childLH (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHH (childLH (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childLH (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101123200 :
    adaptiveCoverCheck 10 (childLL (childLL (childHL (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childHL (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childHL (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101123201 :
    adaptiveCoverCheck 10 (childLH (childLL (childHL (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childHL (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childHL (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101123202 :
    adaptiveCoverCheck 10 (childHL (childLL (childHL (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLL (childHL (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childHL (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101123203 :
    adaptiveCoverCheck 10 (childHH (childLL (childHL (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLL (childHL (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childHL (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101123210 :
    adaptiveCoverCheck 10 (childLL (childLH (childHL (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childHL (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childHL (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101123211 :
    adaptiveCoverCheck 10 (childLH (childLH (childHL (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childHL (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childHL (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101123212 :
    adaptiveCoverCheck 10 (childHL (childLH (childHL (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLH (childHL (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childHL (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101123213 :
    adaptiveCoverCheck 10 (childHH (childLH (childHL (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLH (childHL (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childHL (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf10112322 :
    adaptiveCoverCheck 11 (childHL (childHL (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHL (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf10112323 :
    adaptiveCoverCheck 11 (childHH (childHL (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHL (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101123300 :
    adaptiveCoverCheck 10 (childLL (childLL (childHH (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childHH (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childHH (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101123301 :
    adaptiveCoverCheck 10 (childLH (childLL (childHH (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childHH (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childHH (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101123302 :
    adaptiveCoverCheck 10 (childHL (childLL (childHH (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLL (childHH (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childHH (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101123303 :
    adaptiveCoverCheck 10 (childHH (childLL (childHH (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLL (childHH (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childHH (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101123310 :
    adaptiveCoverCheck 10 (childLL (childLH (childHH (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childHH (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childHH (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101123311 :
    adaptiveCoverCheck 10 (childLH (childLH (childHH (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childHH (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childHH (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101123312 :
    adaptiveCoverCheck 10 (childHL (childLH (childHH (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLH (childHH (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childHH (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101123313 :
    adaptiveCoverCheck 10 (childHH (childLH (childHH (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLH (childHH (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childHH (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf10112332 :
    adaptiveCoverCheck 11 (childHL (childHH (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHH (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf10112333 :
    adaptiveCoverCheck 11 (childHH (childHH (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHH (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1011300 :
    adaptiveCoverCheck 12 (childLL (childLL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLL (childLL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1011301 :
    adaptiveCoverCheck 12 (childLH (childLL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLH (childLL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1011302 :
    adaptiveCoverCheck 12 (childHL (childLL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childHL (childLL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1011303 :
    adaptiveCoverCheck 12 (childHH (childLL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childHH (childLL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1011310 :
    adaptiveCoverCheck 12 (childLL (childLH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLL (childLH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1011311 :
    adaptiveCoverCheck 12 (childLH (childLH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLH (childLH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1011312 :
    adaptiveCoverCheck 12 (childHL (childLH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childHL (childLH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1011313 :
    adaptiveCoverCheck 12 (childHH (childLH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childHH (childLH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101132000 :
    adaptiveCoverCheck 10 (childLL (childLL (childLL (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childLL (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childLL (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101132001 :
    adaptiveCoverCheck 10 (childLH (childLL (childLL (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childLL (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childLL (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101132002 :
    adaptiveCoverCheck 10 (childHL (childLL (childLL (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLL (childLL (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childLL (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101132003 :
    adaptiveCoverCheck 10 (childHH (childLL (childLL (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLL (childLL (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childLL (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101132010 :
    adaptiveCoverCheck 10 (childLL (childLH (childLL (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childLL (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childLL (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101132011 :
    adaptiveCoverCheck 10 (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101132012 :
    adaptiveCoverCheck 10 (childHL (childLH (childLL (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLH (childLL (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childLL (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101132013 :
    adaptiveCoverCheck 10 (childHH (childLH (childLL (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLH (childLL (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childLL (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101132020 :
    adaptiveCoverCheck 10 (childLL (childHL (childLL (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHL (childLL (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHL (childLL (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101132021 :
    adaptiveCoverCheck 10 (childLH (childHL (childLL (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHL (childLL (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHL (childLL (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101132022 :
    adaptiveCoverCheck 10 (childHL (childHL (childLL (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHL (childLL (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childLL (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101132023 :
    adaptiveCoverCheck 10 (childHH (childHL (childLL (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHL (childLL (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childLL (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101132030 :
    adaptiveCoverCheck 10 (childLL (childHH (childLL (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHH (childLL (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHH (childLL (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101132031 :
    adaptiveCoverCheck 10 (childLH (childHH (childLL (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHH (childLL (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHH (childLL (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101132032 :
    adaptiveCoverCheck 10 (childHL (childHH (childLL (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHH (childLL (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childLL (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101132033 :
    adaptiveCoverCheck 10 (childHH (childHH (childLL (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHH (childLL (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childLL (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101132100 :
    adaptiveCoverCheck 10 (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childLH (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101132101 :
    adaptiveCoverCheck 10 (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childLH (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101132102 :
    adaptiveCoverCheck 10 (childHL (childLL (childLH (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLL (childLH (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childLH (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101132103 :
    adaptiveCoverCheck 10 (childHH (childLL (childLH (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLL (childLH (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childLH (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101132110 :
    adaptiveCoverCheck 10 (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childLH (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101132111 :
    adaptiveCoverCheck 10 (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childLH (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101132112 :
    adaptiveCoverCheck 10 (childHL (childLH (childLH (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLH (childLH (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childLH (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101132113 :
    adaptiveCoverCheck 10 (childHH (childLH (childLH (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLH (childLH (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childLH (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101132120 :
    adaptiveCoverCheck 10 (childLL (childHL (childLH (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHL (childLH (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHL (childLH (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101132121 :
    adaptiveCoverCheck 10 (childLH (childHL (childLH (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHL (childLH (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHL (childLH (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101132122 :
    adaptiveCoverCheck 10 (childHL (childHL (childLH (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHL (childLH (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childLH (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101132123 :
    adaptiveCoverCheck 10 (childHH (childHL (childLH (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHL (childLH (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childLH (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101132130 :
    adaptiveCoverCheck 10 (childLL (childHH (childLH (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHH (childLH (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHH (childLH (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101132131 :
    adaptiveCoverCheck 10 (childLH (childHH (childLH (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHH (childLH (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHH (childLH (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101132132 :
    adaptiveCoverCheck 10 (childHL (childHH (childLH (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHH (childLH (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childLH (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101132133 :
    adaptiveCoverCheck 10 (childHH (childHH (childLH (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHH (childLH (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childLH (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101132200 :
    adaptiveCoverCheck 10 (childLL (childLL (childHL (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childHL (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childHL (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101132201 :
    adaptiveCoverCheck 10 (childLH (childLL (childHL (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childHL (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childHL (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101132202 :
    adaptiveCoverCheck 10 (childHL (childLL (childHL (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLL (childHL (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childHL (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101132203 :
    adaptiveCoverCheck 10 (childHH (childLL (childHL (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLL (childHL (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childHL (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101132210 :
    adaptiveCoverCheck 10 (childLL (childLH (childHL (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childHL (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childHL (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101132211 :
    adaptiveCoverCheck 10 (childLH (childLH (childHL (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childHL (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childHL (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101132212 :
    adaptiveCoverCheck 10 (childHL (childLH (childHL (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLH (childHL (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childHL (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101132213 :
    adaptiveCoverCheck 10 (childHH (childLH (childHL (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLH (childHL (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childHL (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf10113222 :
    adaptiveCoverCheck 11 (childHL (childHL (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHL (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf10113223 :
    adaptiveCoverCheck 11 (childHH (childHL (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHL (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101132300 :
    adaptiveCoverCheck 10 (childLL (childLL (childHH (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childHH (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childHH (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101132301 :
    adaptiveCoverCheck 10 (childLH (childLL (childHH (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childHH (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childHH (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101132302 :
    adaptiveCoverCheck 10 (childHL (childLL (childHH (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLL (childHH (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childHH (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101132303 :
    adaptiveCoverCheck 10 (childHH (childLL (childHH (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLL (childHH (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childHH (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101132310 :
    adaptiveCoverCheck 10 (childLL (childLH (childHH (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childHH (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childHH (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101132311 :
    adaptiveCoverCheck 10 (childLH (childLH (childHH (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childHH (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childHH (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101132312 :
    adaptiveCoverCheck 10 (childHL (childLH (childHH (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLH (childHH (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childHH (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101132313 :
    adaptiveCoverCheck 10 (childHH (childLH (childHH (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLH (childHH (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childHH (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf10113232 :
    adaptiveCoverCheck 11 (childHL (childHH (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHH (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf10113233 :
    adaptiveCoverCheck 11 (childHH (childHH (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHH (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101133000 :
    adaptiveCoverCheck 10 (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childLL (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101133001 :
    adaptiveCoverCheck 10 (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childLL (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101133002 :
    adaptiveCoverCheck 10 (childHL (childLL (childLL (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLL (childLL (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childLL (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101133003 :
    adaptiveCoverCheck 10 (childHH (childLL (childLL (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLL (childLL (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childLL (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101133010 :
    adaptiveCoverCheck 10 (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childLL (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101133011 :
    adaptiveCoverCheck 10 (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childLL (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101133012 :
    adaptiveCoverCheck 10 (childHL (childLH (childLL (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLH (childLL (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childLL (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101133013 :
    adaptiveCoverCheck 10 (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101133020 :
    adaptiveCoverCheck 10 (childLL (childHL (childLL (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHL (childLL (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHL (childLL (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101133021 :
    adaptiveCoverCheck 10 (childLH (childHL (childLL (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHL (childLL (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHL (childLL (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101133022 :
    adaptiveCoverCheck 10 (childHL (childHL (childLL (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHL (childLL (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childLL (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101133023 :
    adaptiveCoverCheck 10 (childHH (childHL (childLL (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHL (childLL (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childLL (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101133030 :
    adaptiveCoverCheck 10 (childLL (childHH (childLL (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHH (childLL (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHH (childLL (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101133031 :
    adaptiveCoverCheck 10 (childLH (childHH (childLL (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHH (childLL (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHH (childLL (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101133032 :
    adaptiveCoverCheck 10 (childHL (childHH (childLL (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHH (childLL (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childLL (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101133033 :
    adaptiveCoverCheck 10 (childHH (childHH (childLL (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHH (childLL (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childLL (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101133100 :
    adaptiveCoverCheck 10 (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childLH (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101133101 :
    adaptiveCoverCheck 10 (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childLH (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101133102 :
    adaptiveCoverCheck 10 (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childLH (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101133103 :
    adaptiveCoverCheck 10 (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childLH (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101133110 :
    adaptiveCoverCheck 10 (childLL (childLH (childLH (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childLH (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childLH (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101133111 :
    adaptiveCoverCheck 10 (childLH (childLH (childLH (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childLH (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childLH (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101133112 :
    adaptiveCoverCheck 10 (childHL (childLH (childLH (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLH (childLH (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childLH (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101133113 :
    adaptiveCoverCheck 10 (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childLH (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101133120 :
    adaptiveCoverCheck 10 (childLL (childHL (childLH (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHL (childLH (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHL (childLH (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101133121 :
    adaptiveCoverCheck 10 (childLH (childHL (childLH (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHL (childLH (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHL (childLH (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101133122 :
    adaptiveCoverCheck 10 (childHL (childHL (childLH (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHL (childLH (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childLH (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101133123 :
    adaptiveCoverCheck 10 (childHH (childHL (childLH (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHL (childLH (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childLH (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101133130 :
    adaptiveCoverCheck 10 (childLL (childHH (childLH (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHH (childLH (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHH (childLH (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101133131 :
    adaptiveCoverCheck 10 (childLH (childHH (childLH (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHH (childLH (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHH (childLH (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101133132 :
    adaptiveCoverCheck 10 (childHL (childHH (childLH (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHH (childLH (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childLH (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101133133 :
    adaptiveCoverCheck 10 (childHH (childHH (childLH (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHH (childLH (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childLH (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101133200 :
    adaptiveCoverCheck 10 (childLL (childLL (childHL (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childHL (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childHL (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101133201 :
    adaptiveCoverCheck 10 (childLH (childLL (childHL (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childHL (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childHL (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101133202 :
    adaptiveCoverCheck 10 (childHL (childLL (childHL (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLL (childHL (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childHL (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101133203 :
    adaptiveCoverCheck 10 (childHH (childLL (childHL (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLL (childHL (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childHL (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101133210 :
    adaptiveCoverCheck 10 (childLL (childLH (childHL (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childHL (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childHL (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101133211 :
    adaptiveCoverCheck 10 (childLH (childLH (childHL (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childHL (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childHL (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101133212 :
    adaptiveCoverCheck 10 (childHL (childLH (childHL (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLH (childHL (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childHL (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101133213 :
    adaptiveCoverCheck 10 (childHH (childLH (childHL (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLH (childHL (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childHL (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf10113322 :
    adaptiveCoverCheck 11 (childHL (childHL (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHL (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf10113323 :
    adaptiveCoverCheck 11 (childHH (childHL (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHL (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101133300 :
    adaptiveCoverCheck 10 (childLL (childLL (childHH (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childHH (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childHH (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101133301 :
    adaptiveCoverCheck 10 (childLH (childLL (childHH (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childHH (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childHH (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101133302 :
    adaptiveCoverCheck 10 (childHL (childLL (childHH (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLL (childHH (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childHH (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101133303 :
    adaptiveCoverCheck 10 (childHH (childLL (childHH (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLL (childHH (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childHH (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101133310 :
    adaptiveCoverCheck 10 (childLL (childLH (childHH (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childHH (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childHH (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101133311 :
    adaptiveCoverCheck 10 (childLH (childLH (childHH (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childHH (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childHH (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101133312 :
    adaptiveCoverCheck 10 (childHL (childLH (childHH (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLH (childHH (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childHH (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101133313 :
    adaptiveCoverCheck 10 (childHH (childLH (childHH (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLH (childHH (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childHH (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf10113332 :
    adaptiveCoverCheck 11 (childHL (childHH (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHH (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf10113333 :
    adaptiveCoverCheck 11 (childHH (childHH (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHH (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1012000 :
    adaptiveCoverCheck 12 (childLL (childLL (childLL (childHL (childLH (childLL (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLL (childLL (childLL (childHL (childLH (childLL (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childLL (childHL (childLH (childLL (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1012001 :
    adaptiveCoverCheck 12 (childLH (childLL (childLL (childHL (childLH (childLL (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLH (childLL (childLL (childHL (childLH (childLL (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childLL (childHL (childLH (childLL (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1012002 :
    adaptiveCoverCheck 12 (childHL (childLL (childLL (childHL (childLH (childLL (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childHL (childLL (childLL (childHL (childLH (childLL (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL (childLL (childHL (childLH (childLL (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1012003 :
    adaptiveCoverCheck 12 (childHH (childLL (childLL (childHL (childLH (childLL (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childHH (childLL (childLL (childHL (childLH (childLL (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL (childLL (childHL (childLH (childLL (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1012010 :
    adaptiveCoverCheck 12 (childLL (childLH (childLL (childHL (childLH (childLL (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLL (childLH (childLL (childHL (childLH (childLL (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childLL (childHL (childLH (childLL (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1012011 :
    adaptiveCoverCheck 12 (childLH (childLH (childLL (childHL (childLH (childLL (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLH (childLH (childLL (childHL (childLH (childLL (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childLL (childHL (childLH (childLL (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1012012 :
    adaptiveCoverCheck 12 (childHL (childLH (childLL (childHL (childLH (childLL (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childHL (childLH (childLL (childHL (childLH (childLL (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childLL (childHL (childLH (childLL (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1012013 :
    adaptiveCoverCheck 12 (childHH (childLH (childLL (childHL (childLH (childLL (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childHH (childLH (childLL (childHL (childLH (childLL (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childLL (childHL (childLH (childLL (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101202 :
    adaptiveCoverCheck 13 (childHL (childLL (childHL (childLH (childLL (childLH e24ThetaAboveRoot)))))) = true := by
  have h : ((childHL (childLL (childHL (childLH (childLL (childLH e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLL (childHL (childLH (childLL (childLH e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101203 :
    adaptiveCoverCheck 13 (childHH (childLL (childHL (childLH (childLL (childLH e24ThetaAboveRoot)))))) = true := by
  have h : ((childHH (childLL (childHL (childLH (childLL (childLH e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLL (childHL (childLH (childLL (childLH e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1012100 :
    adaptiveCoverCheck 12 (childLL (childLL (childLH (childHL (childLH (childLL (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLL (childLL (childLH (childHL (childLH (childLL (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childLH (childHL (childLH (childLL (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1012101 :
    adaptiveCoverCheck 12 (childLH (childLL (childLH (childHL (childLH (childLL (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLH (childLL (childLH (childHL (childLH (childLL (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childLH (childHL (childLH (childLL (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1012102 :
    adaptiveCoverCheck 12 (childHL (childLL (childLH (childHL (childLH (childLL (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childHL (childLL (childLH (childHL (childLH (childLL (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL (childLH (childHL (childLH (childLL (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1012103 :
    adaptiveCoverCheck 12 (childHH (childLL (childLH (childHL (childLH (childLL (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childHH (childLL (childLH (childHL (childLH (childLL (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL (childLH (childHL (childLH (childLL (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1012110 :
    adaptiveCoverCheck 12 (childLL (childLH (childLH (childHL (childLH (childLL (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLL (childLH (childLH (childHL (childLH (childLL (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childLH (childHL (childLH (childLL (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1012111 :
    adaptiveCoverCheck 12 (childLH (childLH (childLH (childHL (childLH (childLL (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLH (childLH (childLH (childHL (childLH (childLL (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childLH (childHL (childLH (childLL (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1012112 :
    adaptiveCoverCheck 12 (childHL (childLH (childLH (childHL (childLH (childLL (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childHL (childLH (childLH (childHL (childLH (childLL (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childLH (childHL (childLH (childLL (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1012113 :
    adaptiveCoverCheck 12 (childHH (childLH (childLH (childHL (childLH (childLL (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childHH (childLH (childLH (childHL (childLH (childLL (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childLH (childHL (childLH (childLL (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101212 :
    adaptiveCoverCheck 13 (childHL (childLH (childHL (childLH (childLL (childLH e24ThetaAboveRoot)))))) = true := by
  have h : ((childHL (childLH (childHL (childLH (childLL (childLH e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLH (childHL (childLH (childLL (childLH e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101213 :
    adaptiveCoverCheck 13 (childHH (childLH (childHL (childLH (childLL (childLH e24ThetaAboveRoot)))))) = true := by
  have h : ((childHH (childLH (childHL (childLH (childLL (childLH e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLH (childHL (childLH (childLL (childLH e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf10122 :
    adaptiveCoverCheck 14 (childHL (childHL (childLH (childLL (childLH e24ThetaAboveRoot))))) = true := by
  have h : ((childHL (childHL (childLH (childLL (childLH e24ThetaAboveRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 (childHL (childHL (childLH (childLL (childLH e24ThetaAboveRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf10123 :
    adaptiveCoverCheck 14 (childHH (childHL (childLH (childLL (childLH e24ThetaAboveRoot))))) = true := by
  have h : ((childHH (childHL (childLH (childLL (childLH e24ThetaAboveRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 (childHH (childHL (childLH (childLL (childLH e24ThetaAboveRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1013000 :
    adaptiveCoverCheck 12 (childLL (childLL (childLL (childHH (childLH (childLL (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLL (childLL (childLL (childHH (childLH (childLL (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childLL (childHH (childLH (childLL (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1013001 :
    adaptiveCoverCheck 12 (childLH (childLL (childLL (childHH (childLH (childLL (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLH (childLL (childLL (childHH (childLH (childLL (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childLL (childHH (childLH (childLL (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1013002 :
    adaptiveCoverCheck 12 (childHL (childLL (childLL (childHH (childLH (childLL (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childHL (childLL (childLL (childHH (childLH (childLL (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL (childLL (childHH (childLH (childLL (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1013003 :
    adaptiveCoverCheck 12 (childHH (childLL (childLL (childHH (childLH (childLL (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childHH (childLL (childLL (childHH (childLH (childLL (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL (childLL (childHH (childLH (childLL (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1013010 :
    adaptiveCoverCheck 12 (childLL (childLH (childLL (childHH (childLH (childLL (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLL (childLH (childLL (childHH (childLH (childLL (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childLL (childHH (childLH (childLL (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1013011 :
    adaptiveCoverCheck 12 (childLH (childLH (childLL (childHH (childLH (childLL (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLH (childLH (childLL (childHH (childLH (childLL (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childLL (childHH (childLH (childLL (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1013012 :
    adaptiveCoverCheck 12 (childHL (childLH (childLL (childHH (childLH (childLL (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childHL (childLH (childLL (childHH (childLH (childLL (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childLL (childHH (childLH (childLL (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1013013 :
    adaptiveCoverCheck 12 (childHH (childLH (childLL (childHH (childLH (childLL (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childHH (childLH (childLL (childHH (childLH (childLL (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childLL (childHH (childLH (childLL (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101302 :
    adaptiveCoverCheck 13 (childHL (childLL (childHH (childLH (childLL (childLH e24ThetaAboveRoot)))))) = true := by
  have h : ((childHL (childLL (childHH (childLH (childLL (childLH e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLL (childHH (childLH (childLL (childLH e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101303 :
    adaptiveCoverCheck 13 (childHH (childLL (childHH (childLH (childLL (childLH e24ThetaAboveRoot)))))) = true := by
  have h : ((childHH (childLL (childHH (childLH (childLL (childLH e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLL (childHH (childLH (childLL (childLH e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1013100 :
    adaptiveCoverCheck 12 (childLL (childLL (childLH (childHH (childLH (childLL (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLL (childLL (childLH (childHH (childLH (childLL (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childLH (childHH (childLH (childLL (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1013101 :
    adaptiveCoverCheck 12 (childLH (childLL (childLH (childHH (childLH (childLL (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLH (childLL (childLH (childHH (childLH (childLL (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childLH (childHH (childLH (childLL (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1013102 :
    adaptiveCoverCheck 12 (childHL (childLL (childLH (childHH (childLH (childLL (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childHL (childLL (childLH (childHH (childLH (childLL (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL (childLH (childHH (childLH (childLL (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1013103 :
    adaptiveCoverCheck 12 (childHH (childLL (childLH (childHH (childLH (childLL (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childHH (childLL (childLH (childHH (childLH (childLL (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL (childLH (childHH (childLH (childLL (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1013110 :
    adaptiveCoverCheck 12 (childLL (childLH (childLH (childHH (childLH (childLL (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLL (childLH (childLH (childHH (childLH (childLL (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childLH (childHH (childLH (childLL (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1013111 :
    adaptiveCoverCheck 12 (childLH (childLH (childLH (childHH (childLH (childLL (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLH (childLH (childLH (childHH (childLH (childLL (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childLH (childHH (childLH (childLL (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1013112 :
    adaptiveCoverCheck 12 (childHL (childLH (childLH (childHH (childLH (childLL (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childHL (childLH (childLH (childHH (childLH (childLL (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childLH (childHH (childLH (childLL (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1013113 :
    adaptiveCoverCheck 12 (childHH (childLH (childLH (childHH (childLH (childLL (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childHH (childLH (childLH (childHH (childLH (childLL (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childLH (childHH (childLH (childLL (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101312 :
    adaptiveCoverCheck 13 (childHL (childLH (childHH (childLH (childLL (childLH e24ThetaAboveRoot)))))) = true := by
  have h : ((childHL (childLH (childHH (childLH (childLL (childLH e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLH (childHH (childLH (childLL (childLH e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf101313 :
    adaptiveCoverCheck 13 (childHH (childLH (childHH (childLH (childLL (childLH e24ThetaAboveRoot)))))) = true := by
  have h : ((childHH (childLH (childHH (childLH (childLL (childLH e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLH (childHH (childLH (childLL (childLH e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf10132 :
    adaptiveCoverCheck 14 (childHL (childHH (childLH (childLL (childLH e24ThetaAboveRoot))))) = true := by
  have h : ((childHL (childHH (childLH (childLL (childLH e24ThetaAboveRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 (childHL (childHH (childLH (childLL (childLH e24ThetaAboveRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf10133 :
    adaptiveCoverCheck 14 (childHH (childHH (childLH (childLL (childLH e24ThetaAboveRoot))))) = true := by
  have h : ((childHH (childHH (childLH (childLL (childLH e24ThetaAboveRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 (childHH (childHH (childLH (childLL (childLH e24ThetaAboveRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1020 :
    adaptiveCoverCheck 15 (childLL (childHL (childLL (childLH e24ThetaAboveRoot)))) = true := by
  have h : ((childLL (childHL (childLL (childLH e24ThetaAboveRoot))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 (childLL (childHL (childLL (childLH e24ThetaAboveRoot)))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1021 :
    adaptiveCoverCheck 15 (childLH (childHL (childLL (childLH e24ThetaAboveRoot)))) = true := by
  have h : ((childLH (childHL (childLL (childLH e24ThetaAboveRoot))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 (childLH (childHL (childLL (childLH e24ThetaAboveRoot)))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1022 :
    adaptiveCoverCheck 15 (childHL (childHL (childLL (childLH e24ThetaAboveRoot)))) = true := by
  have h : ((childHL (childHL (childLL (childLH e24ThetaAboveRoot))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 (childHL (childHL (childLL (childLH e24ThetaAboveRoot)))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1023 :
    adaptiveCoverCheck 15 (childHH (childHL (childLL (childLH e24ThetaAboveRoot)))) = true := by
  have h : ((childHH (childHL (childLL (childLH e24ThetaAboveRoot))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 (childHH (childHL (childLL (childLH e24ThetaAboveRoot)))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1030 :
    adaptiveCoverCheck 15 (childLL (childHH (childLL (childLH e24ThetaAboveRoot)))) = true := by
  have h : ((childLL (childHH (childLL (childLH e24ThetaAboveRoot))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 (childLL (childHH (childLL (childLH e24ThetaAboveRoot)))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1031 :
    adaptiveCoverCheck 15 (childLH (childHH (childLL (childLH e24ThetaAboveRoot)))) = true := by
  have h : ((childLH (childHH (childLL (childLH e24ThetaAboveRoot))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 (childLH (childHH (childLL (childLH e24ThetaAboveRoot)))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1032 :
    adaptiveCoverCheck 15 (childHL (childHH (childLL (childLH e24ThetaAboveRoot)))) = true := by
  have h : ((childHL (childHH (childLL (childLH e24ThetaAboveRoot))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 (childHL (childHH (childLL (childLH e24ThetaAboveRoot)))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1033 :
    adaptiveCoverCheck 15 (childHH (childHH (childLL (childLH e24ThetaAboveRoot)))) = true := by
  have h : ((childHH (childHH (childLL (childLH e24ThetaAboveRoot))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 (childHH (childHH (childLL (childLH e24ThetaAboveRoot)))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110000 :
    adaptiveCoverCheck 13 (childLL (childLL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))) = true := by
  have h : ((childLL (childLL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL (childLL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110001 :
    adaptiveCoverCheck 13 (childLH (childLL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))) = true := by
  have h : ((childLH (childLL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH (childLL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110002 :
    adaptiveCoverCheck 13 (childHL (childLL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))) = true := by
  have h : ((childHL (childLL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110003 :
    adaptiveCoverCheck 13 (childHH (childLL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))) = true := by
  have h : ((childHH (childLL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110010 :
    adaptiveCoverCheck 13 (childLL (childLH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))) = true := by
  have h : ((childLL (childLH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL (childLH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110011 :
    adaptiveCoverCheck 13 (childLH (childLH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))) = true := by
  have h : ((childLH (childLH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH (childLH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110012 :
    adaptiveCoverCheck 13 (childHL (childLH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))) = true := by
  have h : ((childHL (childLH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110013 :
    adaptiveCoverCheck 13 (childHH (childLH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))) = true := by
  have h : ((childHH (childLH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1100200 :
    adaptiveCoverCheck 12 (childLL (childLL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLL (childLL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1100201 :
    adaptiveCoverCheck 12 (childLH (childLL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLH (childLL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1100202 :
    adaptiveCoverCheck 12 (childHL (childLL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childHL (childLL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1100203 :
    adaptiveCoverCheck 12 (childHH (childLL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childHH (childLL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1100210 :
    adaptiveCoverCheck 12 (childLL (childLH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLL (childLH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1100211 :
    adaptiveCoverCheck 12 (childLH (childLH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLH (childLH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1100212 :
    adaptiveCoverCheck 12 (childHL (childLH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childHL (childLH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1100213 :
    adaptiveCoverCheck 12 (childHH (childLH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childHH (childLH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11002200 :
    adaptiveCoverCheck 11 (childLL (childLL (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childLL (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLL (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11002201 :
    adaptiveCoverCheck 11 (childLH (childLL (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childLL (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLL (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110022020 :
    adaptiveCoverCheck 10 (childLL (childHL (childLL (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHL (childLL (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHL (childLL (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110022021 :
    adaptiveCoverCheck 10 (childLH (childHL (childLL (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHL (childLL (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHL (childLL (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110022022 :
    adaptiveCoverCheck 10 (childHL (childHL (childLL (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHL (childLL (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childLL (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110022023 :
    adaptiveCoverCheck 10 (childHH (childHL (childLL (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHL (childLL (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childLL (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110022030 :
    adaptiveCoverCheck 10 (childLL (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110022031 :
    adaptiveCoverCheck 10 (childLH (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110022032 :
    adaptiveCoverCheck 10 (childHL (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110022033 :
    adaptiveCoverCheck 10 (childHH (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childLL (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11002210 :
    adaptiveCoverCheck 11 (childLL (childLH (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childLH (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLH (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11002211 :
    adaptiveCoverCheck 11 (childLH (childLH (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childLH (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLH (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110022120 :
    adaptiveCoverCheck 10 (childLL (childHL (childLH (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHL (childLH (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHL (childLH (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110022121 :
    adaptiveCoverCheck 10 (childLH (childHL (childLH (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHL (childLH (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHL (childLH (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110022122 :
    adaptiveCoverCheck 10 (childHL (childHL (childLH (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHL (childLH (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childLH (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110022123 :
    adaptiveCoverCheck 10 (childHH (childHL (childLH (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHL (childLH (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childLH (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110022130 :
    adaptiveCoverCheck 10 (childLL (childHH (childLH (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHH (childLH (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHH (childLH (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110022131 :
    adaptiveCoverCheck 10 (childLH (childHH (childLH (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHH (childLH (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHH (childLH (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110022132 :
    adaptiveCoverCheck 10 (childHL (childHH (childLH (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHH (childLH (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childLH (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110022133 :
    adaptiveCoverCheck 10 (childHH (childHH (childLH (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHH (childLH (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childLH (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110022200 :
    adaptiveCoverCheck 10 (childLL (childLL (childHL (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childHL (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childHL (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110022201 :
    adaptiveCoverCheck 10 (childLH (childLL (childHL (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childHL (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childHL (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110022202 :
    adaptiveCoverCheck 10 (childHL (childLL (childHL (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLL (childHL (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childHL (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110022203 :
    adaptiveCoverCheck 10 (childHH (childLL (childHL (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLL (childHL (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childHL (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110022210 :
    adaptiveCoverCheck 10 (childLL (childLH (childHL (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childHL (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childHL (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110022211 :
    adaptiveCoverCheck 10 (childLH (childLH (childHL (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childHL (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childHL (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110022212 :
    adaptiveCoverCheck 10 (childHL (childLH (childHL (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLH (childHL (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childHL (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110022213 :
    adaptiveCoverCheck 10 (childHH (childLH (childHL (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLH (childHL (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childHL (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11002222 :
    adaptiveCoverCheck 11 (childHL (childHL (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHL (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11002223 :
    adaptiveCoverCheck 11 (childHH (childHL (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHL (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110022300 :
    adaptiveCoverCheck 10 (childLL (childLL (childHH (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childHH (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childHH (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110022301 :
    adaptiveCoverCheck 10 (childLH (childLL (childHH (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childHH (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childHH (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110022302 :
    adaptiveCoverCheck 10 (childHL (childLL (childHH (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLL (childHH (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childHH (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110022303 :
    adaptiveCoverCheck 10 (childHH (childLL (childHH (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLL (childHH (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childHH (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110022310 :
    adaptiveCoverCheck 10 (childLL (childLH (childHH (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childHH (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childHH (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110022311 :
    adaptiveCoverCheck 10 (childLH (childLH (childHH (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childHH (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childHH (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110022312 :
    adaptiveCoverCheck 10 (childHL (childLH (childHH (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLH (childHH (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childHH (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110022313 :
    adaptiveCoverCheck 10 (childHH (childLH (childHH (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLH (childHH (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childHH (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11002232 :
    adaptiveCoverCheck 11 (childHL (childHH (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHH (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11002233 :
    adaptiveCoverCheck 11 (childHH (childHH (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHH (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11002300 :
    adaptiveCoverCheck 11 (childLL (childLL (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childLL (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLL (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11002301 :
    adaptiveCoverCheck 11 (childLH (childLL (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childLL (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLL (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110023020 :
    adaptiveCoverCheck 10 (childLL (childHL (childLL (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHL (childLL (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHL (childLL (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110023021 :
    adaptiveCoverCheck 10 (childLH (childHL (childLL (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHL (childLL (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHL (childLL (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110023022 :
    adaptiveCoverCheck 10 (childHL (childHL (childLL (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHL (childLL (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childLL (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110023023 :
    adaptiveCoverCheck 10 (childHH (childHL (childLL (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHL (childLL (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childLL (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110023030 :
    adaptiveCoverCheck 10 (childLL (childHH (childLL (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHH (childLL (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHH (childLL (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110023031 :
    adaptiveCoverCheck 10 (childLH (childHH (childLL (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHH (childLL (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHH (childLL (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110023032 :
    adaptiveCoverCheck 10 (childHL (childHH (childLL (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHH (childLL (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childLL (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110023033 :
    adaptiveCoverCheck 10 (childHH (childHH (childLL (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHH (childLL (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childLL (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11002310 :
    adaptiveCoverCheck 11 (childLL (childLH (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childLH (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLH (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11002311 :
    adaptiveCoverCheck 11 (childLH (childLH (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childLH (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLH (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110023120 :
    adaptiveCoverCheck 10 (childLL (childHL (childLH (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHL (childLH (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHL (childLH (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110023121 :
    adaptiveCoverCheck 10 (childLH (childHL (childLH (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHL (childLH (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHL (childLH (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110023122 :
    adaptiveCoverCheck 10 (childHL (childHL (childLH (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHL (childLH (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childLH (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110023123 :
    adaptiveCoverCheck 10 (childHH (childHL (childLH (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHL (childLH (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childLH (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110023130 :
    adaptiveCoverCheck 10 (childLL (childHH (childLH (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHH (childLH (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHH (childLH (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110023131 :
    adaptiveCoverCheck 10 (childLH (childHH (childLH (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHH (childLH (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHH (childLH (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110023132 :
    adaptiveCoverCheck 10 (childHL (childHH (childLH (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHH (childLH (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childLH (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110023133 :
    adaptiveCoverCheck 10 (childHH (childHH (childLH (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHH (childLH (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childLH (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110023200 :
    adaptiveCoverCheck 10 (childLL (childLL (childHL (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childHL (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childHL (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110023201 :
    adaptiveCoverCheck 10 (childLH (childLL (childHL (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childHL (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childHL (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110023202 :
    adaptiveCoverCheck 10 (childHL (childLL (childHL (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLL (childHL (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childHL (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110023203 :
    adaptiveCoverCheck 10 (childHH (childLL (childHL (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLL (childHL (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childHL (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110023210 :
    adaptiveCoverCheck 10 (childLL (childLH (childHL (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childHL (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childHL (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110023211 :
    adaptiveCoverCheck 10 (childLH (childLH (childHL (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childHL (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childHL (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110023212 :
    adaptiveCoverCheck 10 (childHL (childLH (childHL (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLH (childHL (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childHL (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110023213 :
    adaptiveCoverCheck 10 (childHH (childLH (childHL (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLH (childHL (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childHL (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11002322 :
    adaptiveCoverCheck 11 (childHL (childHL (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHL (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11002323 :
    adaptiveCoverCheck 11 (childHH (childHL (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHL (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110023300 :
    adaptiveCoverCheck 10 (childLL (childLL (childHH (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childHH (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childHH (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110023301 :
    adaptiveCoverCheck 10 (childLH (childLL (childHH (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childHH (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childHH (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110023302 :
    adaptiveCoverCheck 10 (childHL (childLL (childHH (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLL (childHH (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childHH (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110023303 :
    adaptiveCoverCheck 10 (childHH (childLL (childHH (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLL (childHH (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childHH (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110023310 :
    adaptiveCoverCheck 10 (childLL (childLH (childHH (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childHH (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childHH (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110023311 :
    adaptiveCoverCheck 10 (childLH (childLH (childHH (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childHH (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childHH (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110023312 :
    adaptiveCoverCheck 10 (childHL (childLH (childHH (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLH (childHH (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childHH (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110023313 :
    adaptiveCoverCheck 10 (childHH (childLH (childHH (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLH (childHH (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childHH (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11002332 :
    adaptiveCoverCheck 11 (childHL (childHH (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHH (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11002333 :
    adaptiveCoverCheck 11 (childHH (childHH (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHH (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1100300 :
    adaptiveCoverCheck 12 (childLL (childLL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLL (childLL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1100301 :
    adaptiveCoverCheck 12 (childLH (childLL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLH (childLL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1100302 :
    adaptiveCoverCheck 12 (childHL (childLL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childHL (childLL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1100303 :
    adaptiveCoverCheck 12 (childHH (childLL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childHH (childLL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1100310 :
    adaptiveCoverCheck 12 (childLL (childLH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLL (childLH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1100311 :
    adaptiveCoverCheck 12 (childLH (childLH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLH (childLH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1100312 :
    adaptiveCoverCheck 12 (childHL (childLH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childHL (childLH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1100313 :
    adaptiveCoverCheck 12 (childHH (childLH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childHH (childLH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11003200 :
    adaptiveCoverCheck 11 (childLL (childLL (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childLL (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLL (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11003201 :
    adaptiveCoverCheck 11 (childLH (childLL (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childLL (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLL (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110032020 :
    adaptiveCoverCheck 10 (childLL (childHL (childLL (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHL (childLL (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHL (childLL (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110032021 :
    adaptiveCoverCheck 10 (childLH (childHL (childLL (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHL (childLL (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHL (childLL (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110032022 :
    adaptiveCoverCheck 10 (childHL (childHL (childLL (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHL (childLL (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childLL (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110032023 :
    adaptiveCoverCheck 10 (childHH (childHL (childLL (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHL (childLL (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childLL (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110032030 :
    adaptiveCoverCheck 10 (childLL (childHH (childLL (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHH (childLL (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHH (childLL (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110032031 :
    adaptiveCoverCheck 10 (childLH (childHH (childLL (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHH (childLL (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHH (childLL (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110032032 :
    adaptiveCoverCheck 10 (childHL (childHH (childLL (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHH (childLL (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childLL (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110032033 :
    adaptiveCoverCheck 10 (childHH (childHH (childLL (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHH (childLL (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childLL (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11003210 :
    adaptiveCoverCheck 11 (childLL (childLH (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childLH (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLH (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11003211 :
    adaptiveCoverCheck 11 (childLH (childLH (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childLH (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLH (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110032120 :
    adaptiveCoverCheck 10 (childLL (childHL (childLH (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHL (childLH (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHL (childLH (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110032121 :
    adaptiveCoverCheck 10 (childLH (childHL (childLH (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHL (childLH (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHL (childLH (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110032122 :
    adaptiveCoverCheck 10 (childHL (childHL (childLH (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHL (childLH (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childLH (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110032123 :
    adaptiveCoverCheck 10 (childHH (childHL (childLH (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHL (childLH (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childLH (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110032130 :
    adaptiveCoverCheck 10 (childLL (childHH (childLH (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHH (childLH (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHH (childLH (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110032131 :
    adaptiveCoverCheck 10 (childLH (childHH (childLH (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHH (childLH (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHH (childLH (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110032132 :
    adaptiveCoverCheck 10 (childHL (childHH (childLH (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHH (childLH (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childLH (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110032133 :
    adaptiveCoverCheck 10 (childHH (childHH (childLH (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHH (childLH (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childLH (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110032200 :
    adaptiveCoverCheck 10 (childLL (childLL (childHL (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childHL (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childHL (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110032201 :
    adaptiveCoverCheck 10 (childLH (childLL (childHL (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childHL (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childHL (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110032202 :
    adaptiveCoverCheck 10 (childHL (childLL (childHL (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLL (childHL (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childHL (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110032203 :
    adaptiveCoverCheck 10 (childHH (childLL (childHL (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLL (childHL (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childHL (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110032210 :
    adaptiveCoverCheck 10 (childLL (childLH (childHL (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childHL (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childHL (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110032211 :
    adaptiveCoverCheck 10 (childLH (childLH (childHL (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childHL (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childHL (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110032212 :
    adaptiveCoverCheck 10 (childHL (childLH (childHL (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLH (childHL (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childHL (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110032213 :
    adaptiveCoverCheck 10 (childHH (childLH (childHL (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLH (childHL (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childHL (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11003222 :
    adaptiveCoverCheck 11 (childHL (childHL (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHL (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11003223 :
    adaptiveCoverCheck 11 (childHH (childHL (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHL (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110032300 :
    adaptiveCoverCheck 10 (childLL (childLL (childHH (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childHH (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childHH (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110032301 :
    adaptiveCoverCheck 10 (childLH (childLL (childHH (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childHH (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childHH (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110032302 :
    adaptiveCoverCheck 10 (childHL (childLL (childHH (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLL (childHH (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childHH (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110032303 :
    adaptiveCoverCheck 10 (childHH (childLL (childHH (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLL (childHH (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childHH (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110032310 :
    adaptiveCoverCheck 10 (childLL (childLH (childHH (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childHH (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childHH (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110032311 :
    adaptiveCoverCheck 10 (childLH (childLH (childHH (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childHH (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childHH (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110032312 :
    adaptiveCoverCheck 10 (childHL (childLH (childHH (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLH (childHH (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childHH (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110032313 :
    adaptiveCoverCheck 10 (childHH (childLH (childHH (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLH (childHH (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childHH (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11003232 :
    adaptiveCoverCheck 11 (childHL (childHH (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHH (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11003233 :
    adaptiveCoverCheck 11 (childHH (childHH (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHH (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11003300 :
    adaptiveCoverCheck 11 (childLL (childLL (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childLL (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLL (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11003301 :
    adaptiveCoverCheck 11 (childLH (childLL (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childLL (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLL (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110033020 :
    adaptiveCoverCheck 10 (childLL (childHL (childLL (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHL (childLL (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHL (childLL (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110033021 :
    adaptiveCoverCheck 10 (childLH (childHL (childLL (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHL (childLL (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHL (childLL (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110033022 :
    adaptiveCoverCheck 10 (childHL (childHL (childLL (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHL (childLL (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childLL (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110033023 :
    adaptiveCoverCheck 10 (childHH (childHL (childLL (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHL (childLL (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childLL (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110033030 :
    adaptiveCoverCheck 10 (childLL (childHH (childLL (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHH (childLL (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHH (childLL (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110033031 :
    adaptiveCoverCheck 10 (childLH (childHH (childLL (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHH (childLL (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHH (childLL (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110033032 :
    adaptiveCoverCheck 10 (childHL (childHH (childLL (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHH (childLL (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childLL (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110033033 :
    adaptiveCoverCheck 10 (childHH (childHH (childLL (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHH (childLL (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childLL (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11003310 :
    adaptiveCoverCheck 11 (childLL (childLH (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childLH (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLH (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11003311 :
    adaptiveCoverCheck 11 (childLH (childLH (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childLH (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLH (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110033120 :
    adaptiveCoverCheck 10 (childLL (childHL (childLH (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHL (childLH (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHL (childLH (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110033121 :
    adaptiveCoverCheck 10 (childLH (childHL (childLH (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHL (childLH (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHL (childLH (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110033122 :
    adaptiveCoverCheck 10 (childHL (childHL (childLH (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHL (childLH (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childLH (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110033123 :
    adaptiveCoverCheck 10 (childHH (childHL (childLH (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHL (childLH (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childLH (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110033130 :
    adaptiveCoverCheck 10 (childLL (childHH (childLH (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHH (childLH (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHH (childLH (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110033131 :
    adaptiveCoverCheck 10 (childLH (childHH (childLH (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHH (childLH (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHH (childLH (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110033132 :
    adaptiveCoverCheck 10 (childHL (childHH (childLH (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHH (childLH (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childLH (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110033133 :
    adaptiveCoverCheck 10 (childHH (childHH (childLH (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHH (childLH (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childLH (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110033200 :
    adaptiveCoverCheck 10 (childLL (childLL (childHL (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childHL (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childHL (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110033201 :
    adaptiveCoverCheck 10 (childLH (childLL (childHL (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childHL (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childHL (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110033202 :
    adaptiveCoverCheck 10 (childHL (childLL (childHL (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLL (childHL (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childHL (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110033203 :
    adaptiveCoverCheck 10 (childHH (childLL (childHL (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLL (childHL (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childHL (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110033210 :
    adaptiveCoverCheck 10 (childLL (childLH (childHL (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childHL (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childHL (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110033211 :
    adaptiveCoverCheck 10 (childLH (childLH (childHL (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childHL (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childHL (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110033212 :
    adaptiveCoverCheck 10 (childHL (childLH (childHL (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLH (childHL (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childHL (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110033213 :
    adaptiveCoverCheck 10 (childHH (childLH (childHL (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLH (childHL (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childHL (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11003322 :
    adaptiveCoverCheck 11 (childHL (childHL (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHL (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11003323 :
    adaptiveCoverCheck 11 (childHH (childHL (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHL (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110033300 :
    adaptiveCoverCheck 10 (childLL (childLL (childHH (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childHH (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childHH (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

end PartE
end GerverSofa
