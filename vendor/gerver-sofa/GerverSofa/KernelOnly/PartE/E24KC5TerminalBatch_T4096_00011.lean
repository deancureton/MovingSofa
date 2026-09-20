import GerverSofa.KernelOnly.PartE.E24KC2ProofHelpers

/-! E24KC5 checkpoint-aware kernel batch. -/
noncomputable section

namespace GerverSofa
namespace PartE

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000320222 :
    adaptiveCoverCheck 9 (childHL (childHL (childHL (childLL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childHL (childLL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childHL (childLL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000320223 :
    adaptiveCoverCheck 9 (childHH (childHL (childHL (childLL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childHL (childLL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childHL (childLL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000320230 :
    adaptiveCoverCheck 9 (childLL (childHH (childHL (childLL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childHL (childLL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childHL (childLL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000320231 :
    adaptiveCoverCheck 9 (childLH (childHH (childHL (childLL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childHL (childLL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childHL (childLL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000320232 :
    adaptiveCoverCheck 9 (childHL (childHH (childHL (childLL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childHL (childLL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childHL (childLL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000320233 :
    adaptiveCoverCheck 9 (childHH (childHH (childHL (childLL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childHL (childLL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childHL (childLL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000320300 :
    adaptiveCoverCheck 9 (childLL (childLL (childHH (childLL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHH (childLL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHH (childLL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000320301 :
    adaptiveCoverCheck 9 (childLH (childLL (childHH (childLL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHH (childLL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHH (childLL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000320302 :
    adaptiveCoverCheck 9 (childHL (childLL (childHH (childLL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHH (childLL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHH (childLL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000320303 :
    adaptiveCoverCheck 9 (childHH (childLL (childHH (childLL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHH (childLL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHH (childLL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000320310 :
    adaptiveCoverCheck 9 (childLL (childLH (childHH (childLL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childHH (childLL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHH (childLL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000320311 :
    adaptiveCoverCheck 9 (childLH (childLH (childHH (childLL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childHH (childLL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHH (childLL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000320312 :
    adaptiveCoverCheck 9 (childHL (childLH (childHH (childLL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHH (childLL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHH (childLL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000320313 :
    adaptiveCoverCheck 9 (childHH (childLH (childHH (childLL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHH (childLL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHH (childLL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000320320 :
    adaptiveCoverCheck 9 (childLL (childHL (childHH (childLL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childHH (childLL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childHH (childLL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000320321 :
    adaptiveCoverCheck 9 (childLH (childHL (childHH (childLL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childHH (childLL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childHH (childLL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000320322 :
    adaptiveCoverCheck 9 (childHL (childHL (childHH (childLL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childHH (childLL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childHH (childLL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000320323 :
    adaptiveCoverCheck 9 (childHH (childHL (childHH (childLL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childHH (childLL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childHH (childLL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000320330 :
    adaptiveCoverCheck 9 (childLL (childHH (childHH (childLL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childHH (childLL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childHH (childLL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000320331 :
    adaptiveCoverCheck 9 (childLH (childHH (childHH (childLL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childHH (childLL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childHH (childLL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000320332 :
    adaptiveCoverCheck 9 (childHL (childHH (childHH (childLL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childHH (childLL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childHH (childLL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000320333 :
    adaptiveCoverCheck 9 (childHH (childHH (childHH (childLL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childHH (childLL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childHH (childLL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100032100 :
    adaptiveCoverCheck 10 (childLL (childLL (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100032101 :
    adaptiveCoverCheck 10 (childLH (childLL (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100032102 :
    adaptiveCoverCheck 10 (childHL (childLL (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLL (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100032103 :
    adaptiveCoverCheck 10 (childHH (childLL (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLL (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100032110 :
    adaptiveCoverCheck 10 (childLL (childLH (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100032111 :
    adaptiveCoverCheck 10 (childLH (childLH (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100032112 :
    adaptiveCoverCheck 10 (childHL (childLH (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLH (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100032113 :
    adaptiveCoverCheck 10 (childHH (childLH (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLH (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000321200 :
    adaptiveCoverCheck 9 (childLL (childLL (childHL (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHL (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHL (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000321201 :
    adaptiveCoverCheck 9 (childLH (childLL (childHL (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHL (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHL (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000321202 :
    adaptiveCoverCheck 9 (childHL (childLL (childHL (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHL (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHL (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000321203 :
    adaptiveCoverCheck 9 (childHH (childLL (childHL (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHL (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHL (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000321210 :
    adaptiveCoverCheck 9 (childLL (childLH (childHL (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childHL (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHL (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000321211 :
    adaptiveCoverCheck 9 (childLH (childLH (childHL (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childHL (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHL (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000321212 :
    adaptiveCoverCheck 9 (childHL (childLH (childHL (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHL (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHL (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000321213 :
    adaptiveCoverCheck 9 (childHH (childLH (childHL (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHL (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHL (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000321220 :
    adaptiveCoverCheck 9 (childLL (childHL (childHL (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childHL (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childHL (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000321221 :
    adaptiveCoverCheck 9 (childLH (childHL (childHL (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childHL (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childHL (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000321222 :
    adaptiveCoverCheck 9 (childHL (childHL (childHL (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childHL (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childHL (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000321223 :
    adaptiveCoverCheck 9 (childHH (childHL (childHL (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childHL (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childHL (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000321230 :
    adaptiveCoverCheck 9 (childLL (childHH (childHL (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childHL (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childHL (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000321231 :
    adaptiveCoverCheck 9 (childLH (childHH (childHL (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childHL (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childHL (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000321232 :
    adaptiveCoverCheck 9 (childHL (childHH (childHL (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childHL (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childHL (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000321233 :
    adaptiveCoverCheck 9 (childHH (childHH (childHL (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childHL (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childHL (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000321300 :
    adaptiveCoverCheck 9 (childLL (childLL (childHH (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHH (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHH (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000321301 :
    adaptiveCoverCheck 9 (childLH (childLL (childHH (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHH (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHH (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000321302 :
    adaptiveCoverCheck 9 (childHL (childLL (childHH (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHH (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHH (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000321303 :
    adaptiveCoverCheck 9 (childHH (childLL (childHH (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHH (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHH (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000321310 :
    adaptiveCoverCheck 9 (childLL (childLH (childHH (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childHH (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHH (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000321311 :
    adaptiveCoverCheck 9 (childLH (childLH (childHH (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childHH (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHH (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000321312 :
    adaptiveCoverCheck 9 (childHL (childLH (childHH (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHH (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHH (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000321313 :
    adaptiveCoverCheck 9 (childHH (childLH (childHH (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHH (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHH (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000321320 :
    adaptiveCoverCheck 9 (childLL (childHL (childHH (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childHH (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childHH (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000321321 :
    adaptiveCoverCheck 9 (childLH (childHL (childHH (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childHH (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childHH (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000321322 :
    adaptiveCoverCheck 9 (childHL (childHL (childHH (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childHH (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childHH (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000321323 :
    adaptiveCoverCheck 9 (childHH (childHL (childHH (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childHH (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childHH (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000321330 :
    adaptiveCoverCheck 9 (childLL (childHH (childHH (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childHH (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childHH (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000321331 :
    adaptiveCoverCheck 9 (childLH (childHH (childHH (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childHH (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childHH (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000321332 :
    adaptiveCoverCheck 9 (childHL (childHH (childHH (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childHH (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childHH (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000321333 :
    adaptiveCoverCheck 9 (childHH (childHH (childHH (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childHH (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childHH (childLH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100032200 :
    adaptiveCoverCheck 10 (childLL (childLL (childHL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childHL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childHL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100032201 :
    adaptiveCoverCheck 10 (childLH (childLL (childHL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childHL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childHL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100032202 :
    adaptiveCoverCheck 10 (childHL (childLL (childHL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLL (childHL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childHL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100032203 :
    adaptiveCoverCheck 10 (childHH (childLL (childHL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLL (childHL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childHL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100032210 :
    adaptiveCoverCheck 10 (childLL (childLH (childHL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childHL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childHL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100032211 :
    adaptiveCoverCheck 10 (childLH (childLH (childHL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childHL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childHL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100032212 :
    adaptiveCoverCheck 10 (childHL (childLH (childHL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLH (childHL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childHL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100032213 :
    adaptiveCoverCheck 10 (childHH (childLH (childHL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLH (childHL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childHL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf10003222 :
    adaptiveCoverCheck 11 (childHL (childHL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf10003223 :
    adaptiveCoverCheck 11 (childHH (childHL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100032300 :
    adaptiveCoverCheck 10 (childLL (childLL (childHH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childHH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childHH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100032301 :
    adaptiveCoverCheck 10 (childLH (childLL (childHH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childHH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childHH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100032302 :
    adaptiveCoverCheck 10 (childHL (childLL (childHH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLL (childHH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childHH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100032303 :
    adaptiveCoverCheck 10 (childHH (childLL (childHH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLL (childHH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childHH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100032310 :
    adaptiveCoverCheck 10 (childLL (childLH (childHH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childHH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childHH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100032311 :
    adaptiveCoverCheck 10 (childLH (childLH (childHH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childHH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childHH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100032312 :
    adaptiveCoverCheck 10 (childHL (childLH (childHH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLH (childHH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childHH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100032313 :
    adaptiveCoverCheck 10 (childHH (childLH (childHH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLH (childHH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childHH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf10003232 :
    adaptiveCoverCheck 11 (childHL (childHH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf10003233 :
    adaptiveCoverCheck 11 (childHH (childHH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100033000 :
    adaptiveCoverCheck 10 (childLL (childLL (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100033001 :
    adaptiveCoverCheck 10 (childLH (childLL (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100033002 :
    adaptiveCoverCheck 10 (childHL (childLL (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLL (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100033003 :
    adaptiveCoverCheck 10 (childHH (childLL (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLL (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100033010 :
    adaptiveCoverCheck 10 (childLL (childLH (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100033011 :
    adaptiveCoverCheck 10 (childLH (childLH (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100033012 :
    adaptiveCoverCheck 10 (childHL (childLH (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLH (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100033013 :
    adaptiveCoverCheck 10 (childHH (childLH (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLH (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000330200 :
    adaptiveCoverCheck 9 (childLL (childLL (childHL (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHL (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHL (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000330201 :
    adaptiveCoverCheck 9 (childLH (childLL (childHL (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHL (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHL (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000330202 :
    adaptiveCoverCheck 9 (childHL (childLL (childHL (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHL (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHL (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000330203 :
    adaptiveCoverCheck 9 (childHH (childLL (childHL (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHL (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHL (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000330210 :
    adaptiveCoverCheck 9 (childLL (childLH (childHL (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childHL (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHL (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000330211 :
    adaptiveCoverCheck 9 (childLH (childLH (childHL (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childHL (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHL (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000330212 :
    adaptiveCoverCheck 9 (childHL (childLH (childHL (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHL (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHL (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000330213 :
    adaptiveCoverCheck 9 (childHH (childLH (childHL (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHL (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHL (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000330220 :
    adaptiveCoverCheck 9 (childLL (childHL (childHL (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childHL (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childHL (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000330221 :
    adaptiveCoverCheck 9 (childLH (childHL (childHL (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childHL (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childHL (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000330222 :
    adaptiveCoverCheck 9 (childHL (childHL (childHL (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childHL (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childHL (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000330223 :
    adaptiveCoverCheck 9 (childHH (childHL (childHL (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childHL (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childHL (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000330230 :
    adaptiveCoverCheck 9 (childLL (childHH (childHL (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childHL (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childHL (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000330231 :
    adaptiveCoverCheck 9 (childLH (childHH (childHL (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childHL (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childHL (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000330232 :
    adaptiveCoverCheck 9 (childHL (childHH (childHL (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childHL (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childHL (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000330233 :
    adaptiveCoverCheck 9 (childHH (childHH (childHL (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childHL (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childHL (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000330300 :
    adaptiveCoverCheck 9 (childLL (childLL (childHH (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHH (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHH (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000330301 :
    adaptiveCoverCheck 9 (childLH (childLL (childHH (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHH (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHH (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000330302 :
    adaptiveCoverCheck 9 (childHL (childLL (childHH (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHH (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHH (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000330303 :
    adaptiveCoverCheck 9 (childHH (childLL (childHH (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHH (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHH (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000330310 :
    adaptiveCoverCheck 9 (childLL (childLH (childHH (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childHH (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHH (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000330311 :
    adaptiveCoverCheck 9 (childLH (childLH (childHH (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childHH (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHH (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000330312 :
    adaptiveCoverCheck 9 (childHL (childLH (childHH (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHH (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHH (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000330313 :
    adaptiveCoverCheck 9 (childHH (childLH (childHH (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHH (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHH (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000330320 :
    adaptiveCoverCheck 9 (childLL (childHL (childHH (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childHH (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childHH (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000330321 :
    adaptiveCoverCheck 9 (childLH (childHL (childHH (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childHH (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childHH (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000330322 :
    adaptiveCoverCheck 9 (childHL (childHL (childHH (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childHH (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childHH (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000330323 :
    adaptiveCoverCheck 9 (childHH (childHL (childHH (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childHH (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childHH (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000330330 :
    adaptiveCoverCheck 9 (childLL (childHH (childHH (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childHH (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childHH (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000330331 :
    adaptiveCoverCheck 9 (childLH (childHH (childHH (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childHH (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childHH (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000330332 :
    adaptiveCoverCheck 9 (childHL (childHH (childHH (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childHH (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childHH (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000330333 :
    adaptiveCoverCheck 9 (childHH (childHH (childHH (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childHH (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childHH (childLL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100033100 :
    adaptiveCoverCheck 10 (childLL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100033101 :
    adaptiveCoverCheck 10 (childLH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100033102 :
    adaptiveCoverCheck 10 (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100033103 :
    adaptiveCoverCheck 10 (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100033110 :
    adaptiveCoverCheck 10 (childLL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100033111 :
    adaptiveCoverCheck 10 (childLH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100033112 :
    adaptiveCoverCheck 10 (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100033113 :
    adaptiveCoverCheck 10 (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000331200 :
    adaptiveCoverCheck 9 (childLL (childLL (childHL (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHL (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHL (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000331201 :
    adaptiveCoverCheck 9 (childLH (childLL (childHL (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHL (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHL (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000331202 :
    adaptiveCoverCheck 9 (childHL (childLL (childHL (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHL (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHL (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000331203 :
    adaptiveCoverCheck 9 (childHH (childLL (childHL (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHL (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHL (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000331210 :
    adaptiveCoverCheck 9 (childLL (childLH (childHL (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childHL (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHL (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000331211 :
    adaptiveCoverCheck 9 (childLH (childLH (childHL (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childHL (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHL (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000331212 :
    adaptiveCoverCheck 9 (childHL (childLH (childHL (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHL (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHL (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000331213 :
    adaptiveCoverCheck 9 (childHH (childLH (childHL (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHL (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHL (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000331220 :
    adaptiveCoverCheck 9 (childLL (childHL (childHL (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childHL (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childHL (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000331221 :
    adaptiveCoverCheck 9 (childLH (childHL (childHL (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childHL (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childHL (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000331222 :
    adaptiveCoverCheck 9 (childHL (childHL (childHL (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childHL (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childHL (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000331223 :
    adaptiveCoverCheck 9 (childHH (childHL (childHL (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childHL (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childHL (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000331230 :
    adaptiveCoverCheck 9 (childLL (childHH (childHL (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childHL (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childHL (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000331231 :
    adaptiveCoverCheck 9 (childLH (childHH (childHL (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childHL (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childHL (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000331232 :
    adaptiveCoverCheck 9 (childHL (childHH (childHL (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childHL (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childHL (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000331233 :
    adaptiveCoverCheck 9 (childHH (childHH (childHL (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childHL (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childHL (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000331300 :
    adaptiveCoverCheck 9 (childLL (childLL (childHH (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHH (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHH (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000331301 :
    adaptiveCoverCheck 9 (childLH (childLL (childHH (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHH (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHH (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000331302 :
    adaptiveCoverCheck 9 (childHL (childLL (childHH (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHH (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHH (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000331303 :
    adaptiveCoverCheck 9 (childHH (childLL (childHH (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHH (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHH (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000331310 :
    adaptiveCoverCheck 9 (childLL (childLH (childHH (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childHH (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHH (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000331311 :
    adaptiveCoverCheck 9 (childLH (childLH (childHH (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childHH (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHH (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000331312 :
    adaptiveCoverCheck 9 (childHL (childLH (childHH (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHH (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHH (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000331313 :
    adaptiveCoverCheck 9 (childHH (childLH (childHH (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHH (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHH (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000331320 :
    adaptiveCoverCheck 9 (childLL (childHL (childHH (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childHH (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childHH (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000331321 :
    adaptiveCoverCheck 9 (childLH (childHL (childHH (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childHH (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childHH (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000331322 :
    adaptiveCoverCheck 9 (childHL (childHL (childHH (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childHH (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childHH (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000331323 :
    adaptiveCoverCheck 9 (childHH (childHL (childHH (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childHH (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childHH (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000331330 :
    adaptiveCoverCheck 9 (childLL (childHH (childHH (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childHH (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childHH (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000331331 :
    adaptiveCoverCheck 9 (childLH (childHH (childHH (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childHH (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childHH (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000331332 :
    adaptiveCoverCheck 9 (childHL (childHH (childHH (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childHH (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childHH (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000331333 :
    adaptiveCoverCheck 9 (childHH (childHH (childHH (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childHH (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childHH (childLH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100033200 :
    adaptiveCoverCheck 10 (childLL (childLL (childHL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childHL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childHL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100033201 :
    adaptiveCoverCheck 10 (childLH (childLL (childHL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childHL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childHL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100033202 :
    adaptiveCoverCheck 10 (childHL (childLL (childHL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLL (childHL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childHL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100033203 :
    adaptiveCoverCheck 10 (childHH (childLL (childHL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLL (childHL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childHL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100033210 :
    adaptiveCoverCheck 10 (childLL (childLH (childHL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childHL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childHL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100033211 :
    adaptiveCoverCheck 10 (childLH (childLH (childHL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childHL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childHL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100033212 :
    adaptiveCoverCheck 10 (childHL (childLH (childHL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLH (childHL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childHL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100033213 :
    adaptiveCoverCheck 10 (childHH (childLH (childHL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLH (childHL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childHL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf10003322 :
    adaptiveCoverCheck 11 (childHL (childHL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf10003323 :
    adaptiveCoverCheck 11 (childHH (childHL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100033300 :
    adaptiveCoverCheck 10 (childLL (childLL (childHH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childHH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childHH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100033301 :
    adaptiveCoverCheck 10 (childLH (childLL (childHH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childHH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childHH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100033302 :
    adaptiveCoverCheck 10 (childHL (childLL (childHH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLL (childHH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childHH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100033303 :
    adaptiveCoverCheck 10 (childHH (childLL (childHH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLL (childHH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childHH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100033310 :
    adaptiveCoverCheck 10 (childLL (childLH (childHH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childHH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childHH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000333110 :
    adaptiveCoverCheck 9 (childLL (childLH (childLH (childHH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childLH (childHH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childLH (childHH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000333111 :
    adaptiveCoverCheck 9 (childLH (childLH (childLH (childHH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childLH (childHH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childLH (childHH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000333112 :
    adaptiveCoverCheck 9 (childHL (childLH (childLH (childHH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childLH (childHH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childLH (childHH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1000333113 :
    adaptiveCoverCheck 9 (childHH (childLH (childLH (childHH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childLH (childHH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childLH (childHH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100033312 :
    adaptiveCoverCheck 10 (childHL (childLH (childHH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLH (childHH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childHH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100033313 :
    adaptiveCoverCheck 10 (childHH (childLH (childHH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLH (childHH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childHH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf10003332 :
    adaptiveCoverCheck 11 (childHL (childHH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf10003333 :
    adaptiveCoverCheck 11 (childHH (childHH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100100 :
    adaptiveCoverCheck 13 (childLL (childLL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))) = true := by
  have h : ((childLL (childLL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL (childLL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100101 :
    adaptiveCoverCheck 13 (childLH (childLL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))) = true := by
  have h : ((childLH (childLL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH (childLL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100102 :
    adaptiveCoverCheck 13 (childHL (childLL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))) = true := by
  have h : ((childHL (childLL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100103 :
    adaptiveCoverCheck 13 (childHH (childLL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))) = true := by
  have h : ((childHH (childLL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100110 :
    adaptiveCoverCheck 13 (childLL (childLH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))) = true := by
  have h : ((childLL (childLH (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL (childLH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100111 :
    adaptiveCoverCheck 13 (childLH (childLH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))) = true := by
  have h : ((childLH (childLH (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH (childLH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100112 :
    adaptiveCoverCheck 13 (childHL (childLH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))) = true := by
  have h : ((childHL (childLH (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100113 :
    adaptiveCoverCheck 13 (childHH (childLH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))) = true := by
  have h : ((childHH (childLH (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001200 :
    adaptiveCoverCheck 12 (childLL (childLL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLL (childLL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001201 :
    adaptiveCoverCheck 12 (childLH (childLL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLH (childLL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf10012020 :
    adaptiveCoverCheck 11 (childLL (childHL (childLL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childHL (childLL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHL (childLL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf10012021 :
    adaptiveCoverCheck 11 (childLH (childHL (childLL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childHL (childLL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHL (childLL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf10012022 :
    adaptiveCoverCheck 11 (childHL (childHL (childLL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHL (childLL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childLL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf10012023 :
    adaptiveCoverCheck 11 (childHH (childHL (childLL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHL (childLL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childLL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf10012030 :
    adaptiveCoverCheck 11 (childLL (childHH (childLL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childHH (childLL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHH (childLL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf10012031 :
    adaptiveCoverCheck 11 (childLH (childHH (childLL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childHH (childLL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHH (childLL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf10012032 :
    adaptiveCoverCheck 11 (childHL (childHH (childLL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHH (childLL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childLL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf10012033 :
    adaptiveCoverCheck 11 (childHH (childHH (childLL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHH (childLL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childLL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001210 :
    adaptiveCoverCheck 12 (childLL (childLH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLL (childLH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001211 :
    adaptiveCoverCheck 12 (childLH (childLH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLH (childLH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf10012120 :
    adaptiveCoverCheck 11 (childLL (childHL (childLH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childHL (childLH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHL (childLH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf10012121 :
    adaptiveCoverCheck 11 (childLH (childHL (childLH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childHL (childLH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHL (childLH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf10012122 :
    adaptiveCoverCheck 11 (childHL (childHL (childLH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHL (childLH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childLH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf10012123 :
    adaptiveCoverCheck 11 (childHH (childHL (childLH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHL (childLH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childLH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf10012130 :
    adaptiveCoverCheck 11 (childLL (childHH (childLH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childHH (childLH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHH (childLH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf10012131 :
    adaptiveCoverCheck 11 (childLH (childHH (childLH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childHH (childLH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHH (childLH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf10012132 :
    adaptiveCoverCheck 11 (childHL (childHH (childLH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHH (childLH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childLH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf10012133 :
    adaptiveCoverCheck 11 (childHH (childHH (childLH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHH (childLH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childLH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100122000 :
    adaptiveCoverCheck 10 (childLL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100122001 :
    adaptiveCoverCheck 10 (childLH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100122002 :
    adaptiveCoverCheck 10 (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100122003 :
    adaptiveCoverCheck 10 (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100122010 :
    adaptiveCoverCheck 10 (childLL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100122011 :
    adaptiveCoverCheck 10 (childLH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100122012 :
    adaptiveCoverCheck 10 (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100122013 :
    adaptiveCoverCheck 10 (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001220200 :
    adaptiveCoverCheck 9 (childLL (childLL (childHL (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHL (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHL (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001220201 :
    adaptiveCoverCheck 9 (childLH (childLL (childHL (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHL (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHL (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001220202 :
    adaptiveCoverCheck 9 (childHL (childLL (childHL (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHL (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHL (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001220203 :
    adaptiveCoverCheck 9 (childHH (childLL (childHL (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHL (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHL (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001220210 :
    adaptiveCoverCheck 9 (childLL (childLH (childHL (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childHL (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHL (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001220211 :
    adaptiveCoverCheck 9 (childLH (childLH (childHL (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childHL (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHL (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001220212 :
    adaptiveCoverCheck 9 (childHL (childLH (childHL (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHL (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHL (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001220213 :
    adaptiveCoverCheck 9 (childHH (childLH (childHL (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHL (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHL (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001220220 :
    adaptiveCoverCheck 9 (childLL (childHL (childHL (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childHL (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childHL (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001220221 :
    adaptiveCoverCheck 9 (childLH (childHL (childHL (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childHL (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childHL (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001220222 :
    adaptiveCoverCheck 9 (childHL (childHL (childHL (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childHL (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childHL (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001220223 :
    adaptiveCoverCheck 9 (childHH (childHL (childHL (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childHL (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childHL (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001220230 :
    adaptiveCoverCheck 9 (childLL (childHH (childHL (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childHL (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childHL (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001220231 :
    adaptiveCoverCheck 9 (childLH (childHH (childHL (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childHL (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childHL (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001220232 :
    adaptiveCoverCheck 9 (childHL (childHH (childHL (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childHL (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childHL (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001220233 :
    adaptiveCoverCheck 9 (childHH (childHH (childHL (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childHL (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childHL (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001220300 :
    adaptiveCoverCheck 9 (childLL (childLL (childHH (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHH (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHH (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001220301 :
    adaptiveCoverCheck 9 (childLH (childLL (childHH (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHH (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHH (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001220302 :
    adaptiveCoverCheck 9 (childHL (childLL (childHH (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHH (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHH (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001220303 :
    adaptiveCoverCheck 9 (childHH (childLL (childHH (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHH (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHH (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001220310 :
    adaptiveCoverCheck 9 (childLL (childLH (childHH (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childHH (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHH (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001220311 :
    adaptiveCoverCheck 9 (childLH (childLH (childHH (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childHH (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHH (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001220312 :
    adaptiveCoverCheck 9 (childHL (childLH (childHH (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHH (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHH (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001220313 :
    adaptiveCoverCheck 9 (childHH (childLH (childHH (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHH (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHH (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001220320 :
    adaptiveCoverCheck 9 (childLL (childHL (childHH (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childHH (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childHH (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001220321 :
    adaptiveCoverCheck 9 (childLH (childHL (childHH (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childHH (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childHH (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001220322 :
    adaptiveCoverCheck 9 (childHL (childHL (childHH (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childHH (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childHH (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001220323 :
    adaptiveCoverCheck 9 (childHH (childHL (childHH (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childHH (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childHH (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001220330 :
    adaptiveCoverCheck 9 (childLL (childHH (childHH (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childHH (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childHH (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001220331 :
    adaptiveCoverCheck 9 (childLH (childHH (childHH (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childHH (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childHH (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001220332 :
    adaptiveCoverCheck 9 (childHL (childHH (childHH (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childHH (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childHH (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001220333 :
    adaptiveCoverCheck 9 (childHH (childHH (childHH (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childHH (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childHH (childLL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100122100 :
    adaptiveCoverCheck 10 (childLL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100122101 :
    adaptiveCoverCheck 10 (childLH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100122102 :
    adaptiveCoverCheck 10 (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100122103 :
    adaptiveCoverCheck 10 (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100122110 :
    adaptiveCoverCheck 10 (childLL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100122111 :
    adaptiveCoverCheck 10 (childLH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100122112 :
    adaptiveCoverCheck 10 (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100122113 :
    adaptiveCoverCheck 10 (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001221200 :
    adaptiveCoverCheck 9 (childLL (childLL (childHL (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHL (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHL (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001221201 :
    adaptiveCoverCheck 9 (childLH (childLL (childHL (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHL (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHL (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001221202 :
    adaptiveCoverCheck 9 (childHL (childLL (childHL (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHL (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHL (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001221203 :
    adaptiveCoverCheck 9 (childHH (childLL (childHL (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHL (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHL (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001221210 :
    adaptiveCoverCheck 9 (childLL (childLH (childHL (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childHL (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHL (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001221211 :
    adaptiveCoverCheck 9 (childLH (childLH (childHL (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childHL (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHL (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001221212 :
    adaptiveCoverCheck 9 (childHL (childLH (childHL (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHL (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHL (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001221213 :
    adaptiveCoverCheck 9 (childHH (childLH (childHL (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHL (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHL (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001221220 :
    adaptiveCoverCheck 9 (childLL (childHL (childHL (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childHL (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childHL (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001221221 :
    adaptiveCoverCheck 9 (childLH (childHL (childHL (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childHL (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childHL (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001221222 :
    adaptiveCoverCheck 9 (childHL (childHL (childHL (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childHL (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childHL (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001221223 :
    adaptiveCoverCheck 9 (childHH (childHL (childHL (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childHL (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childHL (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001221230 :
    adaptiveCoverCheck 9 (childLL (childHH (childHL (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childHL (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childHL (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001221231 :
    adaptiveCoverCheck 9 (childLH (childHH (childHL (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childHL (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childHL (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001221232 :
    adaptiveCoverCheck 9 (childHL (childHH (childHL (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childHL (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childHL (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001221233 :
    adaptiveCoverCheck 9 (childHH (childHH (childHL (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childHL (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childHL (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001221300 :
    adaptiveCoverCheck 9 (childLL (childLL (childHH (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHH (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHH (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001221301 :
    adaptiveCoverCheck 9 (childLH (childLL (childHH (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHH (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHH (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001221302 :
    adaptiveCoverCheck 9 (childHL (childLL (childHH (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHH (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHH (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001221303 :
    adaptiveCoverCheck 9 (childHH (childLL (childHH (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHH (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHH (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001221310 :
    adaptiveCoverCheck 9 (childLL (childLH (childHH (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childHH (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHH (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001221311 :
    adaptiveCoverCheck 9 (childLH (childLH (childHH (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childHH (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHH (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001221312 :
    adaptiveCoverCheck 9 (childHL (childLH (childHH (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHH (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHH (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001221313 :
    adaptiveCoverCheck 9 (childHH (childLH (childHH (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHH (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHH (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001221320 :
    adaptiveCoverCheck 9 (childLL (childHL (childHH (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childHH (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childHH (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001221321 :
    adaptiveCoverCheck 9 (childLH (childHL (childHH (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childHH (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childHH (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001221322 :
    adaptiveCoverCheck 9 (childHL (childHL (childHH (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childHH (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childHH (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001221323 :
    adaptiveCoverCheck 9 (childHH (childHL (childHH (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childHH (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childHH (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001221330 :
    adaptiveCoverCheck 9 (childLL (childHH (childHH (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childHH (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childHH (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001221331 :
    adaptiveCoverCheck 9 (childLH (childHH (childHH (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childHH (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childHH (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001221332 :
    adaptiveCoverCheck 9 (childHL (childHH (childHH (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childHH (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childHH (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001221333 :
    adaptiveCoverCheck 9 (childHH (childHH (childHH (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childHH (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childHH (childLH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001222000 :
    adaptiveCoverCheck 9 (childLL (childLL (childLL (childHL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childLL (childHL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childLL (childHL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001222001 :
    adaptiveCoverCheck 9 (childLH (childLL (childLL (childHL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childLL (childHL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childLL (childHL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001222002 :
    adaptiveCoverCheck 9 (childHL (childLL (childLL (childHL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childLL (childHL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childLL (childHL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001222003 :
    adaptiveCoverCheck 9 (childHH (childLL (childLL (childHL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childLL (childHL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childLL (childHL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001222010 :
    adaptiveCoverCheck 9 (childLL (childLH (childLL (childHL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childLL (childHL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childLL (childHL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001222011 :
    adaptiveCoverCheck 9 (childLH (childLH (childLL (childHL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childLL (childHL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childLL (childHL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001222012 :
    adaptiveCoverCheck 9 (childHL (childLH (childLL (childHL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childLL (childHL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childLL (childHL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001222013 :
    adaptiveCoverCheck 9 (childHH (childLH (childLL (childHL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childLL (childHL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childLL (childHL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100122202 :
    adaptiveCoverCheck 10 (childHL (childLL (childHL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLL (childHL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childHL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100122203 :
    adaptiveCoverCheck 10 (childHH (childLL (childHL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLL (childHL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childHL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001222100 :
    adaptiveCoverCheck 9 (childLL (childLL (childLH (childHL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childLH (childHL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childLH (childHL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001222101 :
    adaptiveCoverCheck 9 (childLH (childLL (childLH (childHL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childLH (childHL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childLH (childHL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001222102 :
    adaptiveCoverCheck 9 (childHL (childLL (childLH (childHL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childLH (childHL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childLH (childHL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001222103 :
    adaptiveCoverCheck 9 (childHH (childLL (childLH (childHL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childLH (childHL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childLH (childHL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001222110 :
    adaptiveCoverCheck 9 (childLL (childLH (childLH (childHL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childLH (childHL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childLH (childHL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001222111 :
    adaptiveCoverCheck 9 (childLH (childLH (childLH (childHL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childLH (childHL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childLH (childHL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001222112 :
    adaptiveCoverCheck 9 (childHL (childLH (childLH (childHL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childLH (childHL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childLH (childHL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001222113 :
    adaptiveCoverCheck 9 (childHH (childLH (childLH (childHL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childLH (childHL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childLH (childHL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100122212 :
    adaptiveCoverCheck 10 (childHL (childLH (childHL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLH (childHL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childHL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100122213 :
    adaptiveCoverCheck 10 (childHH (childLH (childHL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLH (childHL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childHL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf10012222 :
    adaptiveCoverCheck 11 (childHL (childHL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf10012223 :
    adaptiveCoverCheck 11 (childHH (childHL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001223000 :
    adaptiveCoverCheck 9 (childLL (childLL (childLL (childHH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childLL (childHH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childLL (childHH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001223001 :
    adaptiveCoverCheck 9 (childLH (childLL (childLL (childHH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childLL (childHH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childLL (childHH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001223002 :
    adaptiveCoverCheck 9 (childHL (childLL (childLL (childHH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childLL (childHH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childLL (childHH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001223003 :
    adaptiveCoverCheck 9 (childHH (childLL (childLL (childHH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childLL (childHH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childLL (childHH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001223010 :
    adaptiveCoverCheck 9 (childLL (childLH (childLL (childHH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childLL (childHH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childLL (childHH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001223011 :
    adaptiveCoverCheck 9 (childLH (childLH (childLL (childHH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childLL (childHH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childLL (childHH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001223012 :
    adaptiveCoverCheck 9 (childHL (childLH (childLL (childHH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childLL (childHH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childLL (childHH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001223013 :
    adaptiveCoverCheck 9 (childHH (childLH (childLL (childHH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childLL (childHH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childLL (childHH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100122302 :
    adaptiveCoverCheck 10 (childHL (childLL (childHH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLL (childHH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childHH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100122303 :
    adaptiveCoverCheck 10 (childHH (childLL (childHH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLL (childHH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childHH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001223100 :
    adaptiveCoverCheck 9 (childLL (childLL (childLH (childHH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childLH (childHH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childLH (childHH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001223101 :
    adaptiveCoverCheck 9 (childLH (childLL (childLH (childHH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childLH (childHH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childLH (childHH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001223102 :
    adaptiveCoverCheck 9 (childHL (childLL (childLH (childHH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childLH (childHH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childLH (childHH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001223103 :
    adaptiveCoverCheck 9 (childHH (childLL (childLH (childHH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childLH (childHH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childLH (childHH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001223110 :
    adaptiveCoverCheck 9 (childLL (childLH (childLH (childHH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childLH (childHH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childLH (childHH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001223111 :
    adaptiveCoverCheck 9 (childLH (childLH (childLH (childHH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childLH (childHH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childLH (childHH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001223112 :
    adaptiveCoverCheck 9 (childHL (childLH (childLH (childHH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childLH (childHH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childLH (childHH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001223113 :
    adaptiveCoverCheck 9 (childHH (childLH (childLH (childHH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childLH (childHH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childLH (childHH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100122312 :
    adaptiveCoverCheck 10 (childHL (childLH (childHH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLH (childHH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childHH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100122313 :
    adaptiveCoverCheck 10 (childHH (childLH (childHH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLH (childHH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childHH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf10012232 :
    adaptiveCoverCheck 11 (childHL (childHH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf10012233 :
    adaptiveCoverCheck 11 (childHH (childHH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100123000 :
    adaptiveCoverCheck 10 (childLL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100123001 :
    adaptiveCoverCheck 10 (childLH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100123002 :
    adaptiveCoverCheck 10 (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100123003 :
    adaptiveCoverCheck 10 (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100123010 :
    adaptiveCoverCheck 10 (childLL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100123011 :
    adaptiveCoverCheck 10 (childLH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100123012 :
    adaptiveCoverCheck 10 (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100123013 :
    adaptiveCoverCheck 10 (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001230200 :
    adaptiveCoverCheck 9 (childLL (childLL (childHL (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHL (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHL (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001230201 :
    adaptiveCoverCheck 9 (childLH (childLL (childHL (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHL (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHL (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001230202 :
    adaptiveCoverCheck 9 (childHL (childLL (childHL (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHL (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHL (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001230203 :
    adaptiveCoverCheck 9 (childHH (childLL (childHL (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHL (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHL (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001230210 :
    adaptiveCoverCheck 9 (childLL (childLH (childHL (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childHL (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHL (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001230211 :
    adaptiveCoverCheck 9 (childLH (childLH (childHL (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childHL (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHL (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001230212 :
    adaptiveCoverCheck 9 (childHL (childLH (childHL (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHL (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHL (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001230213 :
    adaptiveCoverCheck 9 (childHH (childLH (childHL (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHL (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHL (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001230220 :
    adaptiveCoverCheck 9 (childLL (childHL (childHL (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childHL (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childHL (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001230221 :
    adaptiveCoverCheck 9 (childLH (childHL (childHL (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childHL (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childHL (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001230222 :
    adaptiveCoverCheck 9 (childHL (childHL (childHL (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childHL (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childHL (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001230223 :
    adaptiveCoverCheck 9 (childHH (childHL (childHL (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childHL (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childHL (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001230230 :
    adaptiveCoverCheck 9 (childLL (childHH (childHL (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childHL (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childHL (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001230231 :
    adaptiveCoverCheck 9 (childLH (childHH (childHL (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childHL (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childHL (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001230232 :
    adaptiveCoverCheck 9 (childHL (childHH (childHL (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childHL (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childHL (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001230233 :
    adaptiveCoverCheck 9 (childHH (childHH (childHL (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childHL (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childHL (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001230300 :
    adaptiveCoverCheck 9 (childLL (childLL (childHH (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHH (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHH (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001230301 :
    adaptiveCoverCheck 9 (childLH (childLL (childHH (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHH (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHH (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001230302 :
    adaptiveCoverCheck 9 (childHL (childLL (childHH (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHH (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHH (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001230303 :
    adaptiveCoverCheck 9 (childHH (childLL (childHH (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHH (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHH (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001230310 :
    adaptiveCoverCheck 9 (childLL (childLH (childHH (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childHH (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHH (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001230311 :
    adaptiveCoverCheck 9 (childLH (childLH (childHH (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childHH (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHH (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001230312 :
    adaptiveCoverCheck 9 (childHL (childLH (childHH (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHH (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHH (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001230313 :
    adaptiveCoverCheck 9 (childHH (childLH (childHH (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHH (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHH (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001230320 :
    adaptiveCoverCheck 9 (childLL (childHL (childHH (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childHH (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childHH (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001230321 :
    adaptiveCoverCheck 9 (childLH (childHL (childHH (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childHH (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childHH (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001230322 :
    adaptiveCoverCheck 9 (childHL (childHL (childHH (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childHH (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childHH (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001230323 :
    adaptiveCoverCheck 9 (childHH (childHL (childHH (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childHH (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childHH (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001230330 :
    adaptiveCoverCheck 9 (childLL (childHH (childHH (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childHH (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childHH (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001230331 :
    adaptiveCoverCheck 9 (childLH (childHH (childHH (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childHH (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childHH (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001230332 :
    adaptiveCoverCheck 9 (childHL (childHH (childHH (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childHH (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childHH (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001230333 :
    adaptiveCoverCheck 9 (childHH (childHH (childHH (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childHH (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childHH (childLL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100123100 :
    adaptiveCoverCheck 10 (childLL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100123101 :
    adaptiveCoverCheck 10 (childLH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100123102 :
    adaptiveCoverCheck 10 (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100123103 :
    adaptiveCoverCheck 10 (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100123110 :
    adaptiveCoverCheck 10 (childLL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100123111 :
    adaptiveCoverCheck 10 (childLH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100123112 :
    adaptiveCoverCheck 10 (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100123113 :
    adaptiveCoverCheck 10 (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001231200 :
    adaptiveCoverCheck 9 (childLL (childLL (childHL (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHL (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHL (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001231201 :
    adaptiveCoverCheck 9 (childLH (childLL (childHL (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHL (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHL (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001231202 :
    adaptiveCoverCheck 9 (childHL (childLL (childHL (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHL (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHL (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001231203 :
    adaptiveCoverCheck 9 (childHH (childLL (childHL (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHL (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHL (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001231210 :
    adaptiveCoverCheck 9 (childLL (childLH (childHL (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childHL (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHL (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001231211 :
    adaptiveCoverCheck 9 (childLH (childLH (childHL (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childHL (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHL (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001231212 :
    adaptiveCoverCheck 9 (childHL (childLH (childHL (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHL (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHL (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001231213 :
    adaptiveCoverCheck 9 (childHH (childLH (childHL (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHL (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHL (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001231220 :
    adaptiveCoverCheck 9 (childLL (childHL (childHL (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childHL (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childHL (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001231221 :
    adaptiveCoverCheck 9 (childLH (childHL (childHL (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childHL (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childHL (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001231222 :
    adaptiveCoverCheck 9 (childHL (childHL (childHL (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childHL (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childHL (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001231223 :
    adaptiveCoverCheck 9 (childHH (childHL (childHL (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childHL (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childHL (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001231230 :
    adaptiveCoverCheck 9 (childLL (childHH (childHL (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childHL (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childHL (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001231231 :
    adaptiveCoverCheck 9 (childLH (childHH (childHL (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childHL (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childHL (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001231232 :
    adaptiveCoverCheck 9 (childHL (childHH (childHL (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childHL (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childHL (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001231233 :
    adaptiveCoverCheck 9 (childHH (childHH (childHL (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childHL (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childHL (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001231300 :
    adaptiveCoverCheck 9 (childLL (childLL (childHH (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHH (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHH (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001231301 :
    adaptiveCoverCheck 9 (childLH (childLL (childHH (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHH (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHH (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001231302 :
    adaptiveCoverCheck 9 (childHL (childLL (childHH (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHH (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHH (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001231303 :
    adaptiveCoverCheck 9 (childHH (childLL (childHH (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHH (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHH (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001231310 :
    adaptiveCoverCheck 9 (childLL (childLH (childHH (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childHH (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHH (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001231311 :
    adaptiveCoverCheck 9 (childLH (childLH (childHH (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childHH (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHH (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001231312 :
    adaptiveCoverCheck 9 (childHL (childLH (childHH (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHH (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHH (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001231313 :
    adaptiveCoverCheck 9 (childHH (childLH (childHH (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHH (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHH (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001231320 :
    adaptiveCoverCheck 9 (childLL (childHL (childHH (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childHH (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childHH (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001231321 :
    adaptiveCoverCheck 9 (childLH (childHL (childHH (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childHH (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childHH (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001231322 :
    adaptiveCoverCheck 9 (childHL (childHL (childHH (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childHH (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childHH (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001231323 :
    adaptiveCoverCheck 9 (childHH (childHL (childHH (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childHH (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childHH (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001231330 :
    adaptiveCoverCheck 9 (childLL (childHH (childHH (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childHH (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childHH (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001231331 :
    adaptiveCoverCheck 9 (childLH (childHH (childHH (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childHH (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childHH (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001231332 :
    adaptiveCoverCheck 9 (childHL (childHH (childHH (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childHH (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childHH (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001231333 :
    adaptiveCoverCheck 9 (childHH (childHH (childHH (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childHH (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childHH (childLH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001232000 :
    adaptiveCoverCheck 9 (childLL (childLL (childLL (childHL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childLL (childHL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childLL (childHL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001232001 :
    adaptiveCoverCheck 9 (childLH (childLL (childLL (childHL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childLL (childHL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childLL (childHL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001232002 :
    adaptiveCoverCheck 9 (childHL (childLL (childLL (childHL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childLL (childHL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childLL (childHL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001232003 :
    adaptiveCoverCheck 9 (childHH (childLL (childLL (childHL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childLL (childHL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childLL (childHL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001232010 :
    adaptiveCoverCheck 9 (childLL (childLH (childLL (childHL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childLL (childHL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childLL (childHL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001232011 :
    adaptiveCoverCheck 9 (childLH (childLH (childLL (childHL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childLL (childHL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childLL (childHL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001232012 :
    adaptiveCoverCheck 9 (childHL (childLH (childLL (childHL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childLL (childHL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childLL (childHL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001232013 :
    adaptiveCoverCheck 9 (childHH (childLH (childLL (childHL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childLL (childHL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childLL (childHL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100123202 :
    adaptiveCoverCheck 10 (childHL (childLL (childHL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLL (childHL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childHL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100123203 :
    adaptiveCoverCheck 10 (childHH (childLL (childHL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLL (childHL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childHL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001232100 :
    adaptiveCoverCheck 9 (childLL (childLL (childLH (childHL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childLH (childHL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childLH (childHL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001232101 :
    adaptiveCoverCheck 9 (childLH (childLL (childLH (childHL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childLH (childHL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childLH (childHL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001232102 :
    adaptiveCoverCheck 9 (childHL (childLL (childLH (childHL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childLH (childHL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childLH (childHL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001232103 :
    adaptiveCoverCheck 9 (childHH (childLL (childLH (childHL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childLH (childHL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childLH (childHL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001232110 :
    adaptiveCoverCheck 9 (childLL (childLH (childLH (childHL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childLH (childHL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childLH (childHL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001232111 :
    adaptiveCoverCheck 9 (childLH (childLH (childLH (childHL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childLH (childHL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childLH (childHL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001232112 :
    adaptiveCoverCheck 9 (childHL (childLH (childLH (childHL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childLH (childHL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childLH (childHL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001232113 :
    adaptiveCoverCheck 9 (childHH (childLH (childLH (childHL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childLH (childHL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childLH (childHL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100123212 :
    adaptiveCoverCheck 10 (childHL (childLH (childHL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLH (childHL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childHL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100123213 :
    adaptiveCoverCheck 10 (childHH (childLH (childHL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLH (childHL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childHL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf10012322 :
    adaptiveCoverCheck 11 (childHL (childHL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf10012323 :
    adaptiveCoverCheck 11 (childHH (childHL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001233000 :
    adaptiveCoverCheck 9 (childLL (childLL (childLL (childHH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childLL (childHH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childLL (childHH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001233001 :
    adaptiveCoverCheck 9 (childLH (childLL (childLL (childHH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childLL (childHH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childLL (childHH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001233002 :
    adaptiveCoverCheck 9 (childHL (childLL (childLL (childHH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childLL (childHH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childLL (childHH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001233003 :
    adaptiveCoverCheck 9 (childHH (childLL (childLL (childHH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childLL (childHH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childLL (childHH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001233010 :
    adaptiveCoverCheck 9 (childLL (childLH (childLL (childHH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childLL (childHH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childLL (childHH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001233011 :
    adaptiveCoverCheck 9 (childLH (childLH (childLL (childHH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childLL (childHH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childLL (childHH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001233012 :
    adaptiveCoverCheck 9 (childHL (childLH (childLL (childHH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childLL (childHH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childLL (childHH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001233013 :
    adaptiveCoverCheck 9 (childHH (childLH (childLL (childHH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childLL (childHH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childLL (childHH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100123302 :
    adaptiveCoverCheck 10 (childHL (childLL (childHH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLL (childHH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childHH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100123303 :
    adaptiveCoverCheck 10 (childHH (childLL (childHH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLL (childHH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childHH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001233100 :
    adaptiveCoverCheck 9 (childLL (childLL (childLH (childHH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childLH (childHH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childLH (childHH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001233101 :
    adaptiveCoverCheck 9 (childLH (childLL (childLH (childHH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childLH (childHH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childLH (childHH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001233102 :
    adaptiveCoverCheck 9 (childHL (childLL (childLH (childHH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childLH (childHH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childLH (childHH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001233103 :
    adaptiveCoverCheck 9 (childHH (childLL (childLH (childHH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childLH (childHH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childLH (childHH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001233110 :
    adaptiveCoverCheck 9 (childLL (childLH (childLH (childHH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childLH (childHH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childLH (childHH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001233111 :
    adaptiveCoverCheck 9 (childLH (childLH (childLH (childHH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childLH (childHH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childLH (childHH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001233112 :
    adaptiveCoverCheck 9 (childHL (childLH (childLH (childHH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childLH (childHH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childLH (childHH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001233113 :
    adaptiveCoverCheck 9 (childHH (childLH (childLH (childHH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childLH (childHH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childLH (childHH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100123312 :
    adaptiveCoverCheck 10 (childHL (childLH (childHH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLH (childHH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childHH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100123313 :
    adaptiveCoverCheck 10 (childHH (childLH (childHH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLH (childHH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childHH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf10012332 :
    adaptiveCoverCheck 11 (childHL (childHH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf10012333 :
    adaptiveCoverCheck 11 (childHH (childHH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001300 :
    adaptiveCoverCheck 12 (childLL (childLL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLL (childLL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001301 :
    adaptiveCoverCheck 12 (childLH (childLL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLH (childLL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf10013020 :
    adaptiveCoverCheck 11 (childLL (childHL (childLL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childHL (childLL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHL (childLL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf10013021 :
    adaptiveCoverCheck 11 (childLH (childHL (childLL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childHL (childLL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHL (childLL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf10013022 :
    adaptiveCoverCheck 11 (childHL (childHL (childLL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHL (childLL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childLL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf10013023 :
    adaptiveCoverCheck 11 (childHH (childHL (childLL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHL (childLL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childLL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf10013030 :
    adaptiveCoverCheck 11 (childLL (childHH (childLL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childHH (childLL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHH (childLL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf10013031 :
    adaptiveCoverCheck 11 (childLH (childHH (childLL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childHH (childLL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHH (childLL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf10013032 :
    adaptiveCoverCheck 11 (childHL (childHH (childLL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHH (childLL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childLL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf10013033 :
    adaptiveCoverCheck 11 (childHH (childHH (childLL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHH (childLL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childLL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001310 :
    adaptiveCoverCheck 12 (childLL (childLH (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLL (childLH (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001311 :
    adaptiveCoverCheck 12 (childLH (childLH (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLH (childLH (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf10013120 :
    adaptiveCoverCheck 11 (childLL (childHL (childLH (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childHL (childLH (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHL (childLH (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf10013121 :
    adaptiveCoverCheck 11 (childLH (childHL (childLH (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childHL (childLH (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHL (childLH (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf10013122 :
    adaptiveCoverCheck 11 (childHL (childHL (childLH (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHL (childLH (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childLH (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf10013123 :
    adaptiveCoverCheck 11 (childHH (childHL (childLH (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHL (childLH (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childLH (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf10013130 :
    adaptiveCoverCheck 11 (childLL (childHH (childLH (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childHH (childLH (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHH (childLH (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf10013131 :
    adaptiveCoverCheck 11 (childLH (childHH (childLH (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childHH (childLH (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHH (childLH (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf10013132 :
    adaptiveCoverCheck 11 (childHL (childHH (childLH (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHH (childLH (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childLH (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf10013133 :
    adaptiveCoverCheck 11 (childHH (childHH (childLH (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHH (childLH (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childLH (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100132000 :
    adaptiveCoverCheck 10 (childLL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100132001 :
    adaptiveCoverCheck 10 (childLH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100132002 :
    adaptiveCoverCheck 10 (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100132003 :
    adaptiveCoverCheck 10 (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100132010 :
    adaptiveCoverCheck 10 (childLL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100132011 :
    adaptiveCoverCheck 10 (childLH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100132012 :
    adaptiveCoverCheck 10 (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf100132013 :
    adaptiveCoverCheck 10 (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001320200 :
    adaptiveCoverCheck 9 (childLL (childLL (childHL (childLL (childHL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHL (childLL (childHL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHL (childLL (childHL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001320201 :
    adaptiveCoverCheck 9 (childLH (childLL (childHL (childLL (childHL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHL (childLL (childHL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHL (childLL (childHL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001320202 :
    adaptiveCoverCheck 9 (childHL (childLL (childHL (childLL (childHL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHL (childLL (childHL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHL (childLL (childHL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001320203 :
    adaptiveCoverCheck 9 (childHH (childLL (childHL (childLL (childHL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHL (childLL (childHL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHL (childLL (childHL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001320210 :
    adaptiveCoverCheck 9 (childLL (childLH (childHL (childLL (childHL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childHL (childLL (childHL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHL (childLL (childHL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001320211 :
    adaptiveCoverCheck 9 (childLH (childLH (childHL (childLL (childHL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childHL (childLL (childHL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHL (childLL (childHL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001320212 :
    adaptiveCoverCheck 9 (childHL (childLH (childHL (childLL (childHL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHL (childLL (childHL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHL (childLL (childHL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001320213 :
    adaptiveCoverCheck 9 (childHH (childLH (childHL (childLL (childHL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHL (childLL (childHL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHL (childLL (childHL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001320220 :
    adaptiveCoverCheck 9 (childLL (childHL (childHL (childLL (childHL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childHL (childLL (childHL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childHL (childLL (childHL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001320221 :
    adaptiveCoverCheck 9 (childLH (childHL (childHL (childLL (childHL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childHL (childLL (childHL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childHL (childLL (childHL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001320222 :
    adaptiveCoverCheck 9 (childHL (childHL (childHL (childLL (childHL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childHL (childLL (childHL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childHL (childLL (childHL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001320223 :
    adaptiveCoverCheck 9 (childHH (childHL (childHL (childLL (childHL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childHL (childLL (childHL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childHL (childLL (childHL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001320230 :
    adaptiveCoverCheck 9 (childLL (childHH (childHL (childLL (childHL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childHL (childLL (childHL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childHL (childLL (childHL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001320231 :
    adaptiveCoverCheck 9 (childLH (childHH (childHL (childLL (childHL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childHL (childLL (childHL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childHL (childLL (childHL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001320232 :
    adaptiveCoverCheck 9 (childHL (childHH (childHL (childLL (childHL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childHL (childLL (childHL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childHL (childLL (childHL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001320233 :
    adaptiveCoverCheck 9 (childHH (childHH (childHL (childLL (childHL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childHL (childLL (childHL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childHL (childLL (childHL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001320300 :
    adaptiveCoverCheck 9 (childLL (childLL (childHH (childLL (childHL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHH (childLL (childHL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHH (childLL (childHL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001320301 :
    adaptiveCoverCheck 9 (childLH (childLL (childHH (childLL (childHL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHH (childLL (childHL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHH (childLL (childHL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001320302 :
    adaptiveCoverCheck 9 (childHL (childLL (childHH (childLL (childHL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHH (childLL (childHL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHH (childLL (childHL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001320303 :
    adaptiveCoverCheck 9 (childHH (childLL (childHH (childLL (childHL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHH (childLL (childHL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHH (childLL (childHL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001320310 :
    adaptiveCoverCheck 9 (childLL (childLH (childHH (childLL (childHL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childHH (childLL (childHL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHH (childLL (childHL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001320311 :
    adaptiveCoverCheck 9 (childLH (childLH (childHH (childLL (childHL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childHH (childLL (childHL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHH (childLL (childHL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1001320312 :
    adaptiveCoverCheck 9 (childHL (childLH (childHH (childLL (childHL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHH (childLL (childHL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHH (childLL (childHL (childHH (childLH (childLL (childLL (childLH e24ThetaAboveRoot)))))))))) h

end PartE
end GerverSofa
