import GerverSofa.KernelOnly.PartE.E24KC2ProofHelpers

/-! E24KC5 checkpoint-aware kernel batch. -/
noncomputable section

namespace GerverSofa
namespace PartE

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110033301 :
    adaptiveCoverCheck 10 (childLH (childLL (childHH (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childHH (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childHH (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110033302 :
    adaptiveCoverCheck 10 (childHL (childLL (childHH (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLL (childHH (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childHH (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110033303 :
    adaptiveCoverCheck 10 (childHH (childLL (childHH (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLL (childHH (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childHH (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110033310 :
    adaptiveCoverCheck 10 (childLL (childLH (childHH (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childHH (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childHH (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110033311 :
    adaptiveCoverCheck 10 (childLH (childLH (childHH (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childHH (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childHH (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110033312 :
    adaptiveCoverCheck 10 (childHL (childLH (childHH (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLH (childHH (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childHH (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110033313 :
    adaptiveCoverCheck 10 (childHH (childLH (childHH (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLH (childHH (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childHH (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11003332 :
    adaptiveCoverCheck 11 (childHL (childHH (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHH (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11003333 :
    adaptiveCoverCheck 11 (childHH (childHH (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHH (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110100 :
    adaptiveCoverCheck 13 (childLL (childLL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))) = true := by
  have h : ((childLL (childLL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL (childLL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110101 :
    adaptiveCoverCheck 13 (childLH (childLL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))) = true := by
  have h : ((childLH (childLL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH (childLL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110102 :
    adaptiveCoverCheck 13 (childHL (childLL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))) = true := by
  have h : ((childHL (childLL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110103 :
    adaptiveCoverCheck 13 (childHH (childLL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))) = true := by
  have h : ((childHH (childLL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110110 :
    adaptiveCoverCheck 13 (childLL (childLH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))) = true := by
  have h : ((childLL (childLH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL (childLH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110111 :
    adaptiveCoverCheck 13 (childLH (childLH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))) = true := by
  have h : ((childLH (childLH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH (childLH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110112 :
    adaptiveCoverCheck 13 (childHL (childLH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))) = true := by
  have h : ((childHL (childLH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110113 :
    adaptiveCoverCheck 13 (childHH (childLH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))) = true := by
  have h : ((childHH (childLH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1101200 :
    adaptiveCoverCheck 12 (childLL (childLL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLL (childLL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1101201 :
    adaptiveCoverCheck 12 (childLH (childLL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLH (childLL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1101202 :
    adaptiveCoverCheck 12 (childHL (childLL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childHL (childLL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1101203 :
    adaptiveCoverCheck 12 (childHH (childLL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childHH (childLL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1101210 :
    adaptiveCoverCheck 12 (childLL (childLH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLL (childLH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1101211 :
    adaptiveCoverCheck 12 (childLH (childLH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLH (childLH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1101212 :
    adaptiveCoverCheck 12 (childHL (childLH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childHL (childLH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1101213 :
    adaptiveCoverCheck 12 (childHH (childLH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childHH (childLH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11012200 :
    adaptiveCoverCheck 11 (childLL (childLL (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childLL (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLL (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11012201 :
    adaptiveCoverCheck 11 (childLH (childLL (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childLL (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLL (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110122020 :
    adaptiveCoverCheck 10 (childLL (childHL (childLL (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHL (childLL (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHL (childLL (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110122021 :
    adaptiveCoverCheck 10 (childLH (childHL (childLL (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHL (childLL (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHL (childLL (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110122022 :
    adaptiveCoverCheck 10 (childHL (childHL (childLL (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHL (childLL (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childLL (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110122023 :
    adaptiveCoverCheck 10 (childHH (childHL (childLL (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHL (childLL (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childLL (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110122030 :
    adaptiveCoverCheck 10 (childLL (childHH (childLL (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHH (childLL (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHH (childLL (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110122031 :
    adaptiveCoverCheck 10 (childLH (childHH (childLL (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHH (childLL (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHH (childLL (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110122032 :
    adaptiveCoverCheck 10 (childHL (childHH (childLL (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHH (childLL (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childLL (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110122033 :
    adaptiveCoverCheck 10 (childHH (childHH (childLL (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHH (childLL (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childLL (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11012210 :
    adaptiveCoverCheck 11 (childLL (childLH (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childLH (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLH (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11012211 :
    adaptiveCoverCheck 11 (childLH (childLH (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childLH (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLH (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110122120 :
    adaptiveCoverCheck 10 (childLL (childHL (childLH (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHL (childLH (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHL (childLH (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110122121 :
    adaptiveCoverCheck 10 (childLH (childHL (childLH (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHL (childLH (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHL (childLH (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110122122 :
    adaptiveCoverCheck 10 (childHL (childHL (childLH (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHL (childLH (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childLH (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110122123 :
    adaptiveCoverCheck 10 (childHH (childHL (childLH (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHL (childLH (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childLH (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110122130 :
    adaptiveCoverCheck 10 (childLL (childHH (childLH (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHH (childLH (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHH (childLH (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110122131 :
    adaptiveCoverCheck 10 (childLH (childHH (childLH (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHH (childLH (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHH (childLH (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110122132 :
    adaptiveCoverCheck 10 (childHL (childHH (childLH (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHH (childLH (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childLH (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110122133 :
    adaptiveCoverCheck 10 (childHH (childHH (childLH (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHH (childLH (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childLH (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110122200 :
    adaptiveCoverCheck 10 (childLL (childLL (childHL (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childHL (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childHL (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110122201 :
    adaptiveCoverCheck 10 (childLH (childLL (childHL (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childHL (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childHL (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110122202 :
    adaptiveCoverCheck 10 (childHL (childLL (childHL (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLL (childHL (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childHL (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110122203 :
    adaptiveCoverCheck 10 (childHH (childLL (childHL (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLL (childHL (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childHL (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110122210 :
    adaptiveCoverCheck 10 (childLL (childLH (childHL (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childHL (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childHL (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110122211 :
    adaptiveCoverCheck 10 (childLH (childLH (childHL (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childHL (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childHL (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110122212 :
    adaptiveCoverCheck 10 (childHL (childLH (childHL (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLH (childHL (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childHL (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110122213 :
    adaptiveCoverCheck 10 (childHH (childLH (childHL (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLH (childHL (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childHL (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11012222 :
    adaptiveCoverCheck 11 (childHL (childHL (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHL (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11012223 :
    adaptiveCoverCheck 11 (childHH (childHL (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHL (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110122300 :
    adaptiveCoverCheck 10 (childLL (childLL (childHH (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childHH (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childHH (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110122301 :
    adaptiveCoverCheck 10 (childLH (childLL (childHH (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childHH (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childHH (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110122302 :
    adaptiveCoverCheck 10 (childHL (childLL (childHH (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLL (childHH (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childHH (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110122303 :
    adaptiveCoverCheck 10 (childHH (childLL (childHH (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLL (childHH (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childHH (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110122310 :
    adaptiveCoverCheck 10 (childLL (childLH (childHH (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childHH (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childHH (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110122311 :
    adaptiveCoverCheck 10 (childLH (childLH (childHH (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childHH (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childHH (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110122312 :
    adaptiveCoverCheck 10 (childHL (childLH (childHH (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLH (childHH (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childHH (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110122313 :
    adaptiveCoverCheck 10 (childHH (childLH (childHH (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLH (childHH (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childHH (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11012232 :
    adaptiveCoverCheck 11 (childHL (childHH (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHH (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11012233 :
    adaptiveCoverCheck 11 (childHH (childHH (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHH (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11012300 :
    adaptiveCoverCheck 11 (childLL (childLL (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childLL (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLL (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11012301 :
    adaptiveCoverCheck 11 (childLH (childLL (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childLL (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLL (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110123020 :
    adaptiveCoverCheck 10 (childLL (childHL (childLL (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHL (childLL (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHL (childLL (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110123021 :
    adaptiveCoverCheck 10 (childLH (childHL (childLL (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHL (childLL (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHL (childLL (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110123022 :
    adaptiveCoverCheck 10 (childHL (childHL (childLL (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHL (childLL (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childLL (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110123023 :
    adaptiveCoverCheck 10 (childHH (childHL (childLL (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHL (childLL (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childLL (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110123030 :
    adaptiveCoverCheck 10 (childLL (childHH (childLL (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHH (childLL (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHH (childLL (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110123031 :
    adaptiveCoverCheck 10 (childLH (childHH (childLL (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHH (childLL (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHH (childLL (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110123032 :
    adaptiveCoverCheck 10 (childHL (childHH (childLL (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHH (childLL (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childLL (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110123033 :
    adaptiveCoverCheck 10 (childHH (childHH (childLL (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHH (childLL (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childLL (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11012310 :
    adaptiveCoverCheck 11 (childLL (childLH (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childLH (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLH (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11012311 :
    adaptiveCoverCheck 11 (childLH (childLH (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childLH (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLH (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110123120 :
    adaptiveCoverCheck 10 (childLL (childHL (childLH (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHL (childLH (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHL (childLH (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110123121 :
    adaptiveCoverCheck 10 (childLH (childHL (childLH (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHL (childLH (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHL (childLH (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110123122 :
    adaptiveCoverCheck 10 (childHL (childHL (childLH (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHL (childLH (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childLH (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110123123 :
    adaptiveCoverCheck 10 (childHH (childHL (childLH (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHL (childLH (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childLH (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110123130 :
    adaptiveCoverCheck 10 (childLL (childHH (childLH (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHH (childLH (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHH (childLH (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110123131 :
    adaptiveCoverCheck 10 (childLH (childHH (childLH (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHH (childLH (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHH (childLH (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110123132 :
    adaptiveCoverCheck 10 (childHL (childHH (childLH (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHH (childLH (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childLH (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110123133 :
    adaptiveCoverCheck 10 (childHH (childHH (childLH (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHH (childLH (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childLH (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110123200 :
    adaptiveCoverCheck 10 (childLL (childLL (childHL (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childHL (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childHL (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110123201 :
    adaptiveCoverCheck 10 (childLH (childLL (childHL (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childHL (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childHL (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110123202 :
    adaptiveCoverCheck 10 (childHL (childLL (childHL (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLL (childHL (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childHL (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110123203 :
    adaptiveCoverCheck 10 (childHH (childLL (childHL (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLL (childHL (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childHL (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110123210 :
    adaptiveCoverCheck 10 (childLL (childLH (childHL (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childHL (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childHL (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110123211 :
    adaptiveCoverCheck 10 (childLH (childLH (childHL (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childHL (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childHL (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110123212 :
    adaptiveCoverCheck 10 (childHL (childLH (childHL (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLH (childHL (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childHL (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110123213 :
    adaptiveCoverCheck 10 (childHH (childLH (childHL (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLH (childHL (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childHL (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11012322 :
    adaptiveCoverCheck 11 (childHL (childHL (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHL (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11012323 :
    adaptiveCoverCheck 11 (childHH (childHL (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHL (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110123300 :
    adaptiveCoverCheck 10 (childLL (childLL (childHH (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childHH (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childHH (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110123301 :
    adaptiveCoverCheck 10 (childLH (childLL (childHH (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childHH (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childHH (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110123302 :
    adaptiveCoverCheck 10 (childHL (childLL (childHH (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLL (childHH (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childHH (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110123303 :
    adaptiveCoverCheck 10 (childHH (childLL (childHH (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLL (childHH (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childHH (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110123310 :
    adaptiveCoverCheck 10 (childLL (childLH (childHH (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childHH (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childHH (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110123311 :
    adaptiveCoverCheck 10 (childLH (childLH (childHH (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childHH (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childHH (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110123312 :
    adaptiveCoverCheck 10 (childHL (childLH (childHH (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLH (childHH (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childHH (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110123313 :
    adaptiveCoverCheck 10 (childHH (childLH (childHH (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLH (childHH (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childHH (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11012332 :
    adaptiveCoverCheck 11 (childHL (childHH (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHH (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11012333 :
    adaptiveCoverCheck 11 (childHH (childHH (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHH (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1101300 :
    adaptiveCoverCheck 12 (childLL (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLL (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1101301 :
    adaptiveCoverCheck 12 (childLH (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLH (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1101302 :
    adaptiveCoverCheck 12 (childHL (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childHL (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1101303 :
    adaptiveCoverCheck 12 (childHH (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childHH (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1101310 :
    adaptiveCoverCheck 12 (childLL (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLL (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1101311 :
    adaptiveCoverCheck 12 (childLH (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLH (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1101312 :
    adaptiveCoverCheck 12 (childHL (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childHL (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1101313 :
    adaptiveCoverCheck 12 (childHH (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childHH (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11013200 :
    adaptiveCoverCheck 11 (childLL (childLL (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childLL (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLL (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11013201 :
    adaptiveCoverCheck 11 (childLH (childLL (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childLL (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLL (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110132020 :
    adaptiveCoverCheck 10 (childLL (childHL (childLL (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHL (childLL (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHL (childLL (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110132021 :
    adaptiveCoverCheck 10 (childLH (childHL (childLL (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHL (childLL (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHL (childLL (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110132022 :
    adaptiveCoverCheck 10 (childHL (childHL (childLL (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHL (childLL (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childLL (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110132023 :
    adaptiveCoverCheck 10 (childHH (childHL (childLL (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHL (childLL (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childLL (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110132030 :
    adaptiveCoverCheck 10 (childLL (childHH (childLL (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHH (childLL (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHH (childLL (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110132031 :
    adaptiveCoverCheck 10 (childLH (childHH (childLL (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHH (childLL (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHH (childLL (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110132032 :
    adaptiveCoverCheck 10 (childHL (childHH (childLL (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHH (childLL (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childLL (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110132033 :
    adaptiveCoverCheck 10 (childHH (childHH (childLL (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHH (childLL (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childLL (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11013210 :
    adaptiveCoverCheck 11 (childLL (childLH (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childLH (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLH (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11013211 :
    adaptiveCoverCheck 11 (childLH (childLH (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childLH (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLH (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110132120 :
    adaptiveCoverCheck 10 (childLL (childHL (childLH (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHL (childLH (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHL (childLH (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110132121 :
    adaptiveCoverCheck 10 (childLH (childHL (childLH (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHL (childLH (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHL (childLH (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110132122 :
    adaptiveCoverCheck 10 (childHL (childHL (childLH (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHL (childLH (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childLH (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110132123 :
    adaptiveCoverCheck 10 (childHH (childHL (childLH (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHL (childLH (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childLH (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110132130 :
    adaptiveCoverCheck 10 (childLL (childHH (childLH (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHH (childLH (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHH (childLH (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110132131 :
    adaptiveCoverCheck 10 (childLH (childHH (childLH (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHH (childLH (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHH (childLH (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110132132 :
    adaptiveCoverCheck 10 (childHL (childHH (childLH (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHH (childLH (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childLH (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110132133 :
    adaptiveCoverCheck 10 (childHH (childHH (childLH (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHH (childLH (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childLH (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110132200 :
    adaptiveCoverCheck 10 (childLL (childLL (childHL (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childHL (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childHL (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110132201 :
    adaptiveCoverCheck 10 (childLH (childLL (childHL (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childHL (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childHL (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110132202 :
    adaptiveCoverCheck 10 (childHL (childLL (childHL (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLL (childHL (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childHL (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110132203 :
    adaptiveCoverCheck 10 (childHH (childLL (childHL (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLL (childHL (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childHL (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110132210 :
    adaptiveCoverCheck 10 (childLL (childLH (childHL (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childHL (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childHL (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110132211 :
    adaptiveCoverCheck 10 (childLH (childLH (childHL (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childHL (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childHL (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110132212 :
    adaptiveCoverCheck 10 (childHL (childLH (childHL (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLH (childHL (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childHL (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110132213 :
    adaptiveCoverCheck 10 (childHH (childLH (childHL (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLH (childHL (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childHL (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11013222 :
    adaptiveCoverCheck 11 (childHL (childHL (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHL (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11013223 :
    adaptiveCoverCheck 11 (childHH (childHL (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHL (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110132300 :
    adaptiveCoverCheck 10 (childLL (childLL (childHH (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childHH (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childHH (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110132301 :
    adaptiveCoverCheck 10 (childLH (childLL (childHH (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childHH (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childHH (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110132302 :
    adaptiveCoverCheck 10 (childHL (childLL (childHH (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLL (childHH (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childHH (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110132303 :
    adaptiveCoverCheck 10 (childHH (childLL (childHH (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLL (childHH (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childHH (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110132310 :
    adaptiveCoverCheck 10 (childLL (childLH (childHH (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childHH (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childHH (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110132311 :
    adaptiveCoverCheck 10 (childLH (childLH (childHH (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childHH (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childHH (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110132312 :
    adaptiveCoverCheck 10 (childHL (childLH (childHH (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLH (childHH (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childHH (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110132313 :
    adaptiveCoverCheck 10 (childHH (childLH (childHH (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLH (childHH (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childHH (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11013232 :
    adaptiveCoverCheck 11 (childHL (childHH (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHH (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11013233 :
    adaptiveCoverCheck 11 (childHH (childHH (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHH (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11013300 :
    adaptiveCoverCheck 11 (childLL (childLL (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childLL (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLL (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11013301 :
    adaptiveCoverCheck 11 (childLH (childLL (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childLL (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLL (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110133020 :
    adaptiveCoverCheck 10 (childLL (childHL (childLL (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHL (childLL (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHL (childLL (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110133021 :
    adaptiveCoverCheck 10 (childLH (childHL (childLL (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHL (childLL (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHL (childLL (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110133022 :
    adaptiveCoverCheck 10 (childHL (childHL (childLL (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHL (childLL (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childLL (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110133023 :
    adaptiveCoverCheck 10 (childHH (childHL (childLL (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHL (childLL (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childLL (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110133030 :
    adaptiveCoverCheck 10 (childLL (childHH (childLL (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHH (childLL (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHH (childLL (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110133031 :
    adaptiveCoverCheck 10 (childLH (childHH (childLL (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHH (childLL (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHH (childLL (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110133032 :
    adaptiveCoverCheck 10 (childHL (childHH (childLL (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHH (childLL (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childLL (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110133033 :
    adaptiveCoverCheck 10 (childHH (childHH (childLL (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHH (childLL (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childLL (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11013310 :
    adaptiveCoverCheck 11 (childLL (childLH (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childLH (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLH (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11013311 :
    adaptiveCoverCheck 11 (childLH (childLH (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childLH (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLH (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110133120 :
    adaptiveCoverCheck 10 (childLL (childHL (childLH (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHL (childLH (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHL (childLH (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110133121 :
    adaptiveCoverCheck 10 (childLH (childHL (childLH (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHL (childLH (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHL (childLH (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110133122 :
    adaptiveCoverCheck 10 (childHL (childHL (childLH (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHL (childLH (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childLH (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110133123 :
    adaptiveCoverCheck 10 (childHH (childHL (childLH (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHL (childLH (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childLH (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110133130 :
    adaptiveCoverCheck 10 (childLL (childHH (childLH (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHH (childLH (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHH (childLH (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110133131 :
    adaptiveCoverCheck 10 (childLH (childHH (childLH (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHH (childLH (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHH (childLH (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110133132 :
    adaptiveCoverCheck 10 (childHL (childHH (childLH (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHH (childLH (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childLH (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110133133 :
    adaptiveCoverCheck 10 (childHH (childHH (childLH (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHH (childLH (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childLH (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110133200 :
    adaptiveCoverCheck 10 (childLL (childLL (childHL (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childHL (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childHL (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110133201 :
    adaptiveCoverCheck 10 (childLH (childLL (childHL (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childHL (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childHL (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110133202 :
    adaptiveCoverCheck 10 (childHL (childLL (childHL (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLL (childHL (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childHL (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110133203 :
    adaptiveCoverCheck 10 (childHH (childLL (childHL (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLL (childHL (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childHL (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110133210 :
    adaptiveCoverCheck 10 (childLL (childLH (childHL (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childHL (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childHL (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110133211 :
    adaptiveCoverCheck 10 (childLH (childLH (childHL (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childHL (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childHL (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110133212 :
    adaptiveCoverCheck 10 (childHL (childLH (childHL (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLH (childHL (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childHL (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110133213 :
    adaptiveCoverCheck 10 (childHH (childLH (childHL (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLH (childHL (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childHL (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11013322 :
    adaptiveCoverCheck 11 (childHL (childHL (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHL (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11013323 :
    adaptiveCoverCheck 11 (childHH (childHL (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHL (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110133300 :
    adaptiveCoverCheck 10 (childLL (childLL (childHH (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childHH (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childHH (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110133301 :
    adaptiveCoverCheck 10 (childLH (childLL (childHH (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childHH (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childHH (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110133302 :
    adaptiveCoverCheck 10 (childHL (childLL (childHH (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLL (childHH (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childHH (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110133303 :
    adaptiveCoverCheck 10 (childHH (childLL (childHH (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLL (childHH (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childHH (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110133310 :
    adaptiveCoverCheck 10 (childLL (childLH (childHH (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childHH (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childHH (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110133311 :
    adaptiveCoverCheck 10 (childLH (childLH (childHH (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childHH (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childHH (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110133312 :
    adaptiveCoverCheck 10 (childHL (childLH (childHH (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLH (childHH (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childHH (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110133313 :
    adaptiveCoverCheck 10 (childHH (childLH (childHH (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLH (childHH (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childHH (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11013332 :
    adaptiveCoverCheck 11 (childHL (childHH (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHH (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11013333 :
    adaptiveCoverCheck 11 (childHH (childHH (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHH (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1102000 :
    adaptiveCoverCheck 12 (childLL (childLL (childLL (childHL (childLL (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLL (childLL (childLL (childHL (childLL (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childLL (childHL (childLL (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1102001 :
    adaptiveCoverCheck 12 (childLH (childLL (childLL (childHL (childLL (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLH (childLL (childLL (childHL (childLL (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childLL (childHL (childLL (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1102002 :
    adaptiveCoverCheck 12 (childHL (childLL (childLL (childHL (childLL (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childHL (childLL (childLL (childHL (childLL (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL (childLL (childHL (childLL (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1102003 :
    adaptiveCoverCheck 12 (childHH (childLL (childLL (childHL (childLL (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childHH (childLL (childLL (childHL (childLL (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL (childLL (childHL (childLL (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1102010 :
    adaptiveCoverCheck 12 (childLL (childLH (childLL (childHL (childLL (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLL (childLH (childLL (childHL (childLL (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childLL (childHL (childLL (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1102011 :
    adaptiveCoverCheck 12 (childLH (childLH (childLL (childHL (childLL (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLH (childLH (childLL (childHL (childLL (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childLL (childHL (childLL (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1102012 :
    adaptiveCoverCheck 12 (childHL (childLH (childLL (childHL (childLL (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childHL (childLH (childLL (childHL (childLL (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childLL (childHL (childLL (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1102013 :
    adaptiveCoverCheck 12 (childHH (childLH (childLL (childHL (childLL (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childHH (childLH (childLL (childHL (childLL (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childLL (childHL (childLL (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110202 :
    adaptiveCoverCheck 13 (childHL (childLL (childHL (childLL (childLH (childLH e24ThetaAboveRoot)))))) = true := by
  have h : ((childHL (childLL (childHL (childLL (childLH (childLH e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLL (childHL (childLL (childLH (childLH e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110203 :
    adaptiveCoverCheck 13 (childHH (childLL (childHL (childLL (childLH (childLH e24ThetaAboveRoot)))))) = true := by
  have h : ((childHH (childLL (childHL (childLL (childLH (childLH e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLL (childHL (childLL (childLH (childLH e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1102100 :
    adaptiveCoverCheck 12 (childLL (childLL (childLH (childHL (childLL (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLL (childLL (childLH (childHL (childLL (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childLH (childHL (childLL (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1102101 :
    adaptiveCoverCheck 12 (childLH (childLL (childLH (childHL (childLL (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLH (childLL (childLH (childHL (childLL (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childLH (childHL (childLL (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1102102 :
    adaptiveCoverCheck 12 (childHL (childLL (childLH (childHL (childLL (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childHL (childLL (childLH (childHL (childLL (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL (childLH (childHL (childLL (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1102103 :
    adaptiveCoverCheck 12 (childHH (childLL (childLH (childHL (childLL (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childHH (childLL (childLH (childHL (childLL (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL (childLH (childHL (childLL (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1102110 :
    adaptiveCoverCheck 12 (childLL (childLH (childLH (childHL (childLL (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLL (childLH (childLH (childHL (childLL (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childLH (childHL (childLL (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1102111 :
    adaptiveCoverCheck 12 (childLH (childLH (childLH (childHL (childLL (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLH (childLH (childLH (childHL (childLL (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childLH (childHL (childLL (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1102112 :
    adaptiveCoverCheck 12 (childHL (childLH (childLH (childHL (childLL (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childHL (childLH (childLH (childHL (childLL (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childLH (childHL (childLL (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1102113 :
    adaptiveCoverCheck 12 (childHH (childLH (childLH (childHL (childLL (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childHH (childLH (childLH (childHL (childLL (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childLH (childHL (childLL (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110212 :
    adaptiveCoverCheck 13 (childHL (childLH (childHL (childLL (childLH (childLH e24ThetaAboveRoot)))))) = true := by
  have h : ((childHL (childLH (childHL (childLL (childLH (childLH e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLH (childHL (childLL (childLH (childLH e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110213 :
    adaptiveCoverCheck 13 (childHH (childLH (childHL (childLL (childLH (childLH e24ThetaAboveRoot)))))) = true := by
  have h : ((childHH (childLH (childHL (childLL (childLH (childLH e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLH (childHL (childLL (childLH (childLH e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11022 :
    adaptiveCoverCheck 14 (childHL (childHL (childLL (childLH (childLH e24ThetaAboveRoot))))) = true := by
  have h : ((childHL (childHL (childLL (childLH (childLH e24ThetaAboveRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 (childHL (childHL (childLL (childLH (childLH e24ThetaAboveRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11023 :
    adaptiveCoverCheck 14 (childHH (childHL (childLL (childLH (childLH e24ThetaAboveRoot))))) = true := by
  have h : ((childHH (childHL (childLL (childLH (childLH e24ThetaAboveRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 (childHH (childHL (childLL (childLH (childLH e24ThetaAboveRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1103000 :
    adaptiveCoverCheck 12 (childLL (childLL (childLL (childHH (childLL (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLL (childLL (childLL (childHH (childLL (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childLL (childHH (childLL (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1103001 :
    adaptiveCoverCheck 12 (childLH (childLL (childLL (childHH (childLL (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLH (childLL (childLL (childHH (childLL (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childLL (childHH (childLL (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1103002 :
    adaptiveCoverCheck 12 (childHL (childLL (childLL (childHH (childLL (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childHL (childLL (childLL (childHH (childLL (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL (childLL (childHH (childLL (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1103003 :
    adaptiveCoverCheck 12 (childHH (childLL (childLL (childHH (childLL (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childHH (childLL (childLL (childHH (childLL (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL (childLL (childHH (childLL (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1103010 :
    adaptiveCoverCheck 12 (childLL (childLH (childLL (childHH (childLL (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLL (childLH (childLL (childHH (childLL (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childLL (childHH (childLL (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1103011 :
    adaptiveCoverCheck 12 (childLH (childLH (childLL (childHH (childLL (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLH (childLH (childLL (childHH (childLL (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childLL (childHH (childLL (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1103012 :
    adaptiveCoverCheck 12 (childHL (childLH (childLL (childHH (childLL (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childHL (childLH (childLL (childHH (childLL (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childLL (childHH (childLL (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1103013 :
    adaptiveCoverCheck 12 (childHH (childLH (childLL (childHH (childLL (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childHH (childLH (childLL (childHH (childLL (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childLL (childHH (childLL (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110302 :
    adaptiveCoverCheck 13 (childHL (childLL (childHH (childLL (childLH (childLH e24ThetaAboveRoot)))))) = true := by
  have h : ((childHL (childLL (childHH (childLL (childLH (childLH e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLL (childHH (childLL (childLH (childLH e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110303 :
    adaptiveCoverCheck 13 (childHH (childLL (childHH (childLL (childLH (childLH e24ThetaAboveRoot)))))) = true := by
  have h : ((childHH (childLL (childHH (childLL (childLH (childLH e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLL (childHH (childLL (childLH (childLH e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1103100 :
    adaptiveCoverCheck 12 (childLL (childLL (childLH (childHH (childLL (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLL (childLL (childLH (childHH (childLL (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childLH (childHH (childLL (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1103101 :
    adaptiveCoverCheck 12 (childLH (childLL (childLH (childHH (childLL (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLH (childLL (childLH (childHH (childLL (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childLH (childHH (childLL (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1103102 :
    adaptiveCoverCheck 12 (childHL (childLL (childLH (childHH (childLL (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childHL (childLL (childLH (childHH (childLL (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL (childLH (childHH (childLL (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1103103 :
    adaptiveCoverCheck 12 (childHH (childLL (childLH (childHH (childLL (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childHH (childLL (childLH (childHH (childLL (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL (childLH (childHH (childLL (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1103110 :
    adaptiveCoverCheck 12 (childLL (childLH (childLH (childHH (childLL (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLL (childLH (childLH (childHH (childLL (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childLH (childHH (childLL (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1103111 :
    adaptiveCoverCheck 12 (childLH (childLH (childLH (childHH (childLL (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLH (childLH (childLH (childHH (childLL (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childLH (childHH (childLL (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1103112 :
    adaptiveCoverCheck 12 (childHL (childLH (childLH (childHH (childLL (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childHL (childLH (childLH (childHH (childLL (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childLH (childHH (childLL (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1103113 :
    adaptiveCoverCheck 12 (childHH (childLH (childLH (childHH (childLL (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childHH (childLH (childLH (childHH (childLL (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childLH (childHH (childLL (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110312 :
    adaptiveCoverCheck 13 (childHL (childLH (childHH (childLL (childLH (childLH e24ThetaAboveRoot)))))) = true := by
  have h : ((childHL (childLH (childHH (childLL (childLH (childLH e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLH (childHH (childLL (childLH (childLH e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf110313 :
    adaptiveCoverCheck 13 (childHH (childLH (childHH (childLL (childLH (childLH e24ThetaAboveRoot)))))) = true := by
  have h : ((childHH (childLH (childHH (childLL (childLH (childLH e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLH (childHH (childLL (childLH (childLH e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11032 :
    adaptiveCoverCheck 14 (childHL (childHH (childLL (childLH (childLH e24ThetaAboveRoot))))) = true := by
  have h : ((childHL (childHH (childLL (childLH (childLH e24ThetaAboveRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 (childHL (childHH (childLL (childLH (childLH e24ThetaAboveRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11033 :
    adaptiveCoverCheck 14 (childHH (childHH (childLL (childLH (childLH e24ThetaAboveRoot))))) = true := by
  have h : ((childHH (childHH (childLL (childLH (childLH e24ThetaAboveRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 (childHH (childHH (childLL (childLH (childLH e24ThetaAboveRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111000 :
    adaptiveCoverCheck 13 (childLL (childLL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))) = true := by
  have h : ((childLL (childLL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL (childLL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111001 :
    adaptiveCoverCheck 13 (childLH (childLL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))) = true := by
  have h : ((childLH (childLL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH (childLL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111002 :
    adaptiveCoverCheck 13 (childHL (childLL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))) = true := by
  have h : ((childHL (childLL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111003 :
    adaptiveCoverCheck 13 (childHH (childLL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))) = true := by
  have h : ((childHH (childLL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111010 :
    adaptiveCoverCheck 13 (childLL (childLH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))) = true := by
  have h : ((childLL (childLH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL (childLH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111011 :
    adaptiveCoverCheck 13 (childLH (childLH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))) = true := by
  have h : ((childLH (childLH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH (childLH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111012 :
    adaptiveCoverCheck 13 (childHL (childLH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))) = true := by
  have h : ((childHL (childLH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111013 :
    adaptiveCoverCheck 13 (childHH (childLH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))) = true := by
  have h : ((childHH (childLH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1110200 :
    adaptiveCoverCheck 12 (childLL (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLL (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1110201 :
    adaptiveCoverCheck 12 (childLH (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLH (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1110202 :
    adaptiveCoverCheck 12 (childHL (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childHL (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1110203 :
    adaptiveCoverCheck 12 (childHH (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childHH (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1110210 :
    adaptiveCoverCheck 12 (childLL (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLL (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1110211 :
    adaptiveCoverCheck 12 (childLH (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLH (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1110212 :
    adaptiveCoverCheck 12 (childHL (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childHL (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1110213 :
    adaptiveCoverCheck 12 (childHH (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childHH (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11102200 :
    adaptiveCoverCheck 11 (childLL (childLL (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childLL (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLL (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11102201 :
    adaptiveCoverCheck 11 (childLH (childLL (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childLL (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLL (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111022020 :
    adaptiveCoverCheck 10 (childLL (childHL (childLL (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHL (childLL (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHL (childLL (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111022021 :
    adaptiveCoverCheck 10 (childLH (childHL (childLL (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHL (childLL (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHL (childLL (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111022022 :
    adaptiveCoverCheck 10 (childHL (childHL (childLL (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHL (childLL (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childLL (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111022023 :
    adaptiveCoverCheck 10 (childHH (childHL (childLL (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHL (childLL (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childLL (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111022030 :
    adaptiveCoverCheck 10 (childLL (childHH (childLL (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHH (childLL (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHH (childLL (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111022031 :
    adaptiveCoverCheck 10 (childLH (childHH (childLL (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHH (childLL (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHH (childLL (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111022032 :
    adaptiveCoverCheck 10 (childHL (childHH (childLL (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHH (childLL (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childLL (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111022033 :
    adaptiveCoverCheck 10 (childHH (childHH (childLL (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHH (childLL (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childLL (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11102210 :
    adaptiveCoverCheck 11 (childLL (childLH (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childLH (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLH (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11102211 :
    adaptiveCoverCheck 11 (childLH (childLH (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childLH (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLH (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111022120 :
    adaptiveCoverCheck 10 (childLL (childHL (childLH (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHL (childLH (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHL (childLH (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111022121 :
    adaptiveCoverCheck 10 (childLH (childHL (childLH (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHL (childLH (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHL (childLH (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111022122 :
    adaptiveCoverCheck 10 (childHL (childHL (childLH (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHL (childLH (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childLH (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111022123 :
    adaptiveCoverCheck 10 (childHH (childHL (childLH (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHL (childLH (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childLH (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111022130 :
    adaptiveCoverCheck 10 (childLL (childHH (childLH (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHH (childLH (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHH (childLH (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111022131 :
    adaptiveCoverCheck 10 (childLH (childHH (childLH (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHH (childLH (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHH (childLH (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111022132 :
    adaptiveCoverCheck 10 (childHL (childHH (childLH (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHH (childLH (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childLH (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111022133 :
    adaptiveCoverCheck 10 (childHH (childHH (childLH (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHH (childLH (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childLH (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111022200 :
    adaptiveCoverCheck 10 (childLL (childLL (childHL (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childHL (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childHL (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111022201 :
    adaptiveCoverCheck 10 (childLH (childLL (childHL (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childHL (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childHL (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111022202 :
    adaptiveCoverCheck 10 (childHL (childLL (childHL (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLL (childHL (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childHL (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111022203 :
    adaptiveCoverCheck 10 (childHH (childLL (childHL (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLL (childHL (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childHL (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111022210 :
    adaptiveCoverCheck 10 (childLL (childLH (childHL (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childHL (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childHL (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111022211 :
    adaptiveCoverCheck 10 (childLH (childLH (childHL (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childHL (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childHL (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111022212 :
    adaptiveCoverCheck 10 (childHL (childLH (childHL (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLH (childHL (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childHL (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111022213 :
    adaptiveCoverCheck 10 (childHH (childLH (childHL (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLH (childHL (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childHL (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11102222 :
    adaptiveCoverCheck 11 (childHL (childHL (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHL (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11102223 :
    adaptiveCoverCheck 11 (childHH (childHL (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHL (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111022300 :
    adaptiveCoverCheck 10 (childLL (childLL (childHH (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childHH (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childHH (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111022301 :
    adaptiveCoverCheck 10 (childLH (childLL (childHH (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childHH (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childHH (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111022302 :
    adaptiveCoverCheck 10 (childHL (childLL (childHH (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLL (childHH (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childHH (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111022303 :
    adaptiveCoverCheck 10 (childHH (childLL (childHH (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLL (childHH (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childHH (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111022310 :
    adaptiveCoverCheck 10 (childLL (childLH (childHH (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childHH (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childHH (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111022311 :
    adaptiveCoverCheck 10 (childLH (childLH (childHH (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childHH (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childHH (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111022312 :
    adaptiveCoverCheck 10 (childHL (childLH (childHH (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLH (childHH (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childHH (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111022313 :
    adaptiveCoverCheck 10 (childHH (childLH (childHH (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLH (childHH (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childHH (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11102232 :
    adaptiveCoverCheck 11 (childHL (childHH (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHH (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11102233 :
    adaptiveCoverCheck 11 (childHH (childHH (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHH (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11102300 :
    adaptiveCoverCheck 11 (childLL (childLL (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childLL (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLL (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11102301 :
    adaptiveCoverCheck 11 (childLH (childLL (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childLL (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLL (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111023020 :
    adaptiveCoverCheck 10 (childLL (childHL (childLL (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHL (childLL (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHL (childLL (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111023021 :
    adaptiveCoverCheck 10 (childLH (childHL (childLL (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHL (childLL (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHL (childLL (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111023022 :
    adaptiveCoverCheck 10 (childHL (childHL (childLL (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHL (childLL (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childLL (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111023023 :
    adaptiveCoverCheck 10 (childHH (childHL (childLL (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHL (childLL (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childLL (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111023030 :
    adaptiveCoverCheck 10 (childLL (childHH (childLL (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHH (childLL (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHH (childLL (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111023031 :
    adaptiveCoverCheck 10 (childLH (childHH (childLL (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHH (childLL (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHH (childLL (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111023032 :
    adaptiveCoverCheck 10 (childHL (childHH (childLL (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHH (childLL (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childLL (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111023033 :
    adaptiveCoverCheck 10 (childHH (childHH (childLL (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHH (childLL (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childLL (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11102310 :
    adaptiveCoverCheck 11 (childLL (childLH (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childLH (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLH (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11102311 :
    adaptiveCoverCheck 11 (childLH (childLH (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childLH (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLH (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111023120 :
    adaptiveCoverCheck 10 (childLL (childHL (childLH (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHL (childLH (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHL (childLH (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111023121 :
    adaptiveCoverCheck 10 (childLH (childHL (childLH (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHL (childLH (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHL (childLH (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111023122 :
    adaptiveCoverCheck 10 (childHL (childHL (childLH (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHL (childLH (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childLH (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111023123 :
    adaptiveCoverCheck 10 (childHH (childHL (childLH (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHL (childLH (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childLH (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111023130 :
    adaptiveCoverCheck 10 (childLL (childHH (childLH (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHH (childLH (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHH (childLH (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111023131 :
    adaptiveCoverCheck 10 (childLH (childHH (childLH (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHH (childLH (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHH (childLH (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111023132 :
    adaptiveCoverCheck 10 (childHL (childHH (childLH (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHH (childLH (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childLH (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111023133 :
    adaptiveCoverCheck 10 (childHH (childHH (childLH (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHH (childLH (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childLH (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111023200 :
    adaptiveCoverCheck 10 (childLL (childLL (childHL (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childHL (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childHL (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111023201 :
    adaptiveCoverCheck 10 (childLH (childLL (childHL (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childHL (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childHL (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111023202 :
    adaptiveCoverCheck 10 (childHL (childLL (childHL (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLL (childHL (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childHL (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111023203 :
    adaptiveCoverCheck 10 (childHH (childLL (childHL (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLL (childHL (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childHL (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111023210 :
    adaptiveCoverCheck 10 (childLL (childLH (childHL (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childHL (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childHL (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111023211 :
    adaptiveCoverCheck 10 (childLH (childLH (childHL (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childHL (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childHL (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111023212 :
    adaptiveCoverCheck 10 (childHL (childLH (childHL (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLH (childHL (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childHL (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111023213 :
    adaptiveCoverCheck 10 (childHH (childLH (childHL (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLH (childHL (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childHL (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11102322 :
    adaptiveCoverCheck 11 (childHL (childHL (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHL (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11102323 :
    adaptiveCoverCheck 11 (childHH (childHL (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHL (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111023300 :
    adaptiveCoverCheck 10 (childLL (childLL (childHH (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childHH (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childHH (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111023301 :
    adaptiveCoverCheck 10 (childLH (childLL (childHH (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childHH (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childHH (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111023302 :
    adaptiveCoverCheck 10 (childHL (childLL (childHH (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLL (childHH (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childHH (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111023303 :
    adaptiveCoverCheck 10 (childHH (childLL (childHH (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLL (childHH (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childHH (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111023310 :
    adaptiveCoverCheck 10 (childLL (childLH (childHH (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childHH (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childHH (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111023311 :
    adaptiveCoverCheck 10 (childLH (childLH (childHH (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childHH (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childHH (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111023312 :
    adaptiveCoverCheck 10 (childHL (childLH (childHH (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLH (childHH (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childHH (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111023313 :
    adaptiveCoverCheck 10 (childHH (childLH (childHH (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLH (childHH (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childHH (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11102332 :
    adaptiveCoverCheck 11 (childHL (childHH (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHH (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11102333 :
    adaptiveCoverCheck 11 (childHH (childHH (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHH (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1110300 :
    adaptiveCoverCheck 12 (childLL (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLL (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1110301 :
    adaptiveCoverCheck 12 (childLH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1110302 :
    adaptiveCoverCheck 12 (childHL (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childHL (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1110303 :
    adaptiveCoverCheck 12 (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1110310 :
    adaptiveCoverCheck 12 (childLL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1110311 :
    adaptiveCoverCheck 12 (childLH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1110312 :
    adaptiveCoverCheck 12 (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1110313 :
    adaptiveCoverCheck 12 (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11103200 :
    adaptiveCoverCheck 11 (childLL (childLL (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childLL (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLL (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11103201 :
    adaptiveCoverCheck 11 (childLH (childLL (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childLL (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLL (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111032020 :
    adaptiveCoverCheck 10 (childLL (childHL (childLL (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHL (childLL (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHL (childLL (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111032021 :
    adaptiveCoverCheck 10 (childLH (childHL (childLL (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHL (childLL (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHL (childLL (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111032022 :
    adaptiveCoverCheck 10 (childHL (childHL (childLL (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHL (childLL (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childLL (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111032023 :
    adaptiveCoverCheck 10 (childHH (childHL (childLL (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHL (childLL (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childLL (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111032030 :
    adaptiveCoverCheck 10 (childLL (childHH (childLL (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHH (childLL (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHH (childLL (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111032031 :
    adaptiveCoverCheck 10 (childLH (childHH (childLL (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHH (childLL (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHH (childLL (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111032032 :
    adaptiveCoverCheck 10 (childHL (childHH (childLL (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHH (childLL (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childLL (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111032033 :
    adaptiveCoverCheck 10 (childHH (childHH (childLL (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHH (childLL (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childLL (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11103210 :
    adaptiveCoverCheck 11 (childLL (childLH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childLH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11103211 :
    adaptiveCoverCheck 11 (childLH (childLH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childLH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111032120 :
    adaptiveCoverCheck 10 (childLL (childHL (childLH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHL (childLH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHL (childLH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111032121 :
    adaptiveCoverCheck 10 (childLH (childHL (childLH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHL (childLH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHL (childLH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111032122 :
    adaptiveCoverCheck 10 (childHL (childHL (childLH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHL (childLH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childLH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111032123 :
    adaptiveCoverCheck 10 (childHH (childHL (childLH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHL (childLH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childLH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111032130 :
    adaptiveCoverCheck 10 (childLL (childHH (childLH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHH (childLH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHH (childLH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111032131 :
    adaptiveCoverCheck 10 (childLH (childHH (childLH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHH (childLH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHH (childLH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111032132 :
    adaptiveCoverCheck 10 (childHL (childHH (childLH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHH (childLH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childLH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111032133 :
    adaptiveCoverCheck 10 (childHH (childHH (childLH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHH (childLH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childLH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111032200 :
    adaptiveCoverCheck 10 (childLL (childLL (childHL (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childHL (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childHL (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111032201 :
    adaptiveCoverCheck 10 (childLH (childLL (childHL (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childHL (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childHL (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111032202 :
    adaptiveCoverCheck 10 (childHL (childLL (childHL (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLL (childHL (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childHL (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111032203 :
    adaptiveCoverCheck 10 (childHH (childLL (childHL (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLL (childHL (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childHL (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111032210 :
    adaptiveCoverCheck 10 (childLL (childLH (childHL (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childHL (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childHL (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111032211 :
    adaptiveCoverCheck 10 (childLH (childLH (childHL (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childHL (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childHL (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111032212 :
    adaptiveCoverCheck 10 (childHL (childLH (childHL (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLH (childHL (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childHL (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111032213 :
    adaptiveCoverCheck 10 (childHH (childLH (childHL (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLH (childHL (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childHL (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11103222 :
    adaptiveCoverCheck 11 (childHL (childHL (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHL (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11103223 :
    adaptiveCoverCheck 11 (childHH (childHL (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHL (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111032300 :
    adaptiveCoverCheck 10 (childLL (childLL (childHH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childHH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childHH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111032301 :
    adaptiveCoverCheck 10 (childLH (childLL (childHH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childHH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childHH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111032302 :
    adaptiveCoverCheck 10 (childHL (childLL (childHH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLL (childHH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childHH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111032303 :
    adaptiveCoverCheck 10 (childHH (childLL (childHH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLL (childHH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childHH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111032310 :
    adaptiveCoverCheck 10 (childLL (childLH (childHH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childHH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childHH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111032311 :
    adaptiveCoverCheck 10 (childLH (childLH (childHH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childHH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childHH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111032312 :
    adaptiveCoverCheck 10 (childHL (childLH (childHH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLH (childHH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childHH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111032313 :
    adaptiveCoverCheck 10 (childHH (childLH (childHH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLH (childHH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childHH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11103232 :
    adaptiveCoverCheck 11 (childHL (childHH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11103233 :
    adaptiveCoverCheck 11 (childHH (childHH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11103300 :
    adaptiveCoverCheck 11 (childLL (childLL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childLL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11103301 :
    adaptiveCoverCheck 11 (childLH (childLL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childLL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111033020 :
    adaptiveCoverCheck 10 (childLL (childHL (childLL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHL (childLL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHL (childLL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111033021 :
    adaptiveCoverCheck 10 (childLH (childHL (childLL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHL (childLL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHL (childLL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111033022 :
    adaptiveCoverCheck 10 (childHL (childHL (childLL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHL (childLL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childLL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111033023 :
    adaptiveCoverCheck 10 (childHH (childHL (childLL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHL (childLL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childLL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111033030 :
    adaptiveCoverCheck 10 (childLL (childHH (childLL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHH (childLL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHH (childLL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111033031 :
    adaptiveCoverCheck 10 (childLH (childHH (childLL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHH (childLL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHH (childLL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111033032 :
    adaptiveCoverCheck 10 (childHL (childHH (childLL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHH (childLL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childLL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111033033 :
    adaptiveCoverCheck 10 (childHH (childHH (childLL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHH (childLL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childLL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11103310 :
    adaptiveCoverCheck 11 (childLL (childLH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childLH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11103311 :
    adaptiveCoverCheck 11 (childLH (childLH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childLH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111033120 :
    adaptiveCoverCheck 10 (childLL (childHL (childLH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHL (childLH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHL (childLH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111033121 :
    adaptiveCoverCheck 10 (childLH (childHL (childLH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHL (childLH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHL (childLH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111033122 :
    adaptiveCoverCheck 10 (childHL (childHL (childLH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHL (childLH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childLH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111033123 :
    adaptiveCoverCheck 10 (childHH (childHL (childLH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHL (childLH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childLH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111033130 :
    adaptiveCoverCheck 10 (childLL (childHH (childLH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHH (childLH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHH (childLH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111033131 :
    adaptiveCoverCheck 10 (childLH (childHH (childLH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHH (childLH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHH (childLH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111033132 :
    adaptiveCoverCheck 10 (childHL (childHH (childLH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHH (childLH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childLH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111033133 :
    adaptiveCoverCheck 10 (childHH (childHH (childLH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHH (childLH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childLH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111033200 :
    adaptiveCoverCheck 10 (childLL (childLL (childHL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childHL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childHL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111033201 :
    adaptiveCoverCheck 10 (childLH (childLL (childHL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childHL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childHL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111033202 :
    adaptiveCoverCheck 10 (childHL (childLL (childHL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLL (childHL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childHL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111033203 :
    adaptiveCoverCheck 10 (childHH (childLL (childHL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLL (childHL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childHL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111033210 :
    adaptiveCoverCheck 10 (childLL (childLH (childHL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childHL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childHL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111033211 :
    adaptiveCoverCheck 10 (childLH (childLH (childHL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childHL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childHL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111033212 :
    adaptiveCoverCheck 10 (childHL (childLH (childHL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLH (childHL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childHL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111033213 :
    adaptiveCoverCheck 10 (childHH (childLH (childHL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLH (childHL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childHL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11103322 :
    adaptiveCoverCheck 11 (childHL (childHL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11103323 :
    adaptiveCoverCheck 11 (childHH (childHL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111033300 :
    adaptiveCoverCheck 10 (childLL (childLL (childHH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childHH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childHH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111033301 :
    adaptiveCoverCheck 10 (childLH (childLL (childHH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childHH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childHH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111033302 :
    adaptiveCoverCheck 10 (childHL (childLL (childHH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLL (childHH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childHH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111033303 :
    adaptiveCoverCheck 10 (childHH (childLL (childHH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLL (childHH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childHH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111033310 :
    adaptiveCoverCheck 10 (childLL (childLH (childHH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childHH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childHH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111033311 :
    adaptiveCoverCheck 10 (childLH (childLH (childHH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childHH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childHH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111033312 :
    adaptiveCoverCheck 10 (childHL (childLH (childHH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLH (childHH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childHH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111033313 :
    adaptiveCoverCheck 10 (childHH (childLH (childHH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLH (childHH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childHH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11103332 :
    adaptiveCoverCheck 11 (childHL (childHH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11103333 :
    adaptiveCoverCheck 11 (childHH (childHH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111100 :
    adaptiveCoverCheck 13 (childLL (childLL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))) = true := by
  have h : ((childLL (childLL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL (childLL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111101 :
    adaptiveCoverCheck 13 (childLH (childLL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))) = true := by
  have h : ((childLH (childLL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH (childLL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111102 :
    adaptiveCoverCheck 13 (childHL (childLL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))) = true := by
  have h : ((childHL (childLL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111103 :
    adaptiveCoverCheck 13 (childHH (childLL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))) = true := by
  have h : ((childHH (childLL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111110 :
    adaptiveCoverCheck 13 (childLL (childLH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))) = true := by
  have h : ((childLL (childLH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL (childLH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111111 :
    adaptiveCoverCheck 13 (childLH (childLH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))) = true := by
  have h : ((childLH (childLH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH (childLH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111112 :
    adaptiveCoverCheck 13 (childHL (childLH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))) = true := by
  have h : ((childHL (childLH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111113 :
    adaptiveCoverCheck 13 (childHH (childLH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))) = true := by
  have h : ((childHH (childLH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1111200 :
    adaptiveCoverCheck 12 (childLL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1111201 :
    adaptiveCoverCheck 12 (childLH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1111202 :
    adaptiveCoverCheck 12 (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1111203 :
    adaptiveCoverCheck 12 (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1111210 :
    adaptiveCoverCheck 12 (childLL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1111211 :
    adaptiveCoverCheck 12 (childLH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1111212 :
    adaptiveCoverCheck 12 (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1111213 :
    adaptiveCoverCheck 12 (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11112200 :
    adaptiveCoverCheck 11 (childLL (childLL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childLL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11112201 :
    adaptiveCoverCheck 11 (childLH (childLL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childLL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111122020 :
    adaptiveCoverCheck 10 (childLL (childHL (childLL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHL (childLL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHL (childLL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111122021 :
    adaptiveCoverCheck 10 (childLH (childHL (childLL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHL (childLL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHL (childLL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111122022 :
    adaptiveCoverCheck 10 (childHL (childHL (childLL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHL (childLL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childLL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111122023 :
    adaptiveCoverCheck 10 (childHH (childHL (childLL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHL (childLL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childLL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111122030 :
    adaptiveCoverCheck 10 (childLL (childHH (childLL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHH (childLL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHH (childLL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111122031 :
    adaptiveCoverCheck 10 (childLH (childHH (childLL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHH (childLL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHH (childLL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111122032 :
    adaptiveCoverCheck 10 (childHL (childHH (childLL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHH (childLL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childLL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111122033 :
    adaptiveCoverCheck 10 (childHH (childHH (childLL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHH (childLL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childLL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11112210 :
    adaptiveCoverCheck 11 (childLL (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11112211 :
    adaptiveCoverCheck 11 (childLH (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111122120 :
    adaptiveCoverCheck 10 (childLL (childHL (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHL (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHL (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111122121 :
    adaptiveCoverCheck 10 (childLH (childHL (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHL (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHL (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111122122 :
    adaptiveCoverCheck 10 (childHL (childHL (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHL (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111122123 :
    adaptiveCoverCheck 10 (childHH (childHL (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHL (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111122130 :
    adaptiveCoverCheck 10 (childLL (childHH (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHH (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHH (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111122131 :
    adaptiveCoverCheck 10 (childLH (childHH (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHH (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHH (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111122132 :
    adaptiveCoverCheck 10 (childHL (childHH (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHH (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111122133 :
    adaptiveCoverCheck 10 (childHH (childHH (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHH (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111122200 :
    adaptiveCoverCheck 10 (childLL (childLL (childHL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childHL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childHL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111122201 :
    adaptiveCoverCheck 10 (childLH (childLL (childHL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childHL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childHL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111122202 :
    adaptiveCoverCheck 10 (childHL (childLL (childHL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLL (childHL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childHL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111122203 :
    adaptiveCoverCheck 10 (childHH (childLL (childHL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLL (childHL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childHL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111122210 :
    adaptiveCoverCheck 10 (childLL (childLH (childHL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childHL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childHL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111122211 :
    adaptiveCoverCheck 10 (childLH (childLH (childHL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childHL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childHL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111122212 :
    adaptiveCoverCheck 10 (childHL (childLH (childHL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLH (childHL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childHL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111122213 :
    adaptiveCoverCheck 10 (childHH (childLH (childHL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLH (childHL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childHL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11112222 :
    adaptiveCoverCheck 11 (childHL (childHL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11112223 :
    adaptiveCoverCheck 11 (childHH (childHL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111122300 :
    adaptiveCoverCheck 10 (childLL (childLL (childHH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childHH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childHH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111122301 :
    adaptiveCoverCheck 10 (childLH (childLL (childHH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childHH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childHH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111122302 :
    adaptiveCoverCheck 10 (childHL (childLL (childHH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLL (childHH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childHH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111122303 :
    adaptiveCoverCheck 10 (childHH (childLL (childHH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLL (childHH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childHH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111122310 :
    adaptiveCoverCheck 10 (childLL (childLH (childHH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childHH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childHH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111122311 :
    adaptiveCoverCheck 10 (childLH (childLH (childHH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childHH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childHH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111122312 :
    adaptiveCoverCheck 10 (childHL (childLH (childHH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLH (childHH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childHH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111122313 :
    adaptiveCoverCheck 10 (childHH (childLH (childHH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLH (childHH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childHH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11112232 :
    adaptiveCoverCheck 11 (childHL (childHH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11112233 :
    adaptiveCoverCheck 11 (childHH (childHH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11112300 :
    adaptiveCoverCheck 11 (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11112301 :
    adaptiveCoverCheck 11 (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111123020 :
    adaptiveCoverCheck 10 (childLL (childHL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111123021 :
    adaptiveCoverCheck 10 (childLH (childHL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111123022 :
    adaptiveCoverCheck 10 (childHL (childHL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111123023 :
    adaptiveCoverCheck 10 (childHH (childHL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111123030 :
    adaptiveCoverCheck 10 (childLL (childHH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111123031 :
    adaptiveCoverCheck 10 (childLH (childHH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111123032 :
    adaptiveCoverCheck 10 (childHL (childHH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111123033 :
    adaptiveCoverCheck 10 (childHH (childHH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11112310 :
    adaptiveCoverCheck 11 (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11112311 :
    adaptiveCoverCheck 11 (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111123120 :
    adaptiveCoverCheck 10 (childLL (childHL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111123121 :
    adaptiveCoverCheck 10 (childLH (childHL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111123122 :
    adaptiveCoverCheck 10 (childHL (childHL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111123123 :
    adaptiveCoverCheck 10 (childHH (childHL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111123130 :
    adaptiveCoverCheck 10 (childLL (childHH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111123131 :
    adaptiveCoverCheck 10 (childLH (childHH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111123132 :
    adaptiveCoverCheck 10 (childHL (childHH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111123133 :
    adaptiveCoverCheck 10 (childHH (childHH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111123200 :
    adaptiveCoverCheck 10 (childLL (childLL (childHL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childHL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childHL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111123201 :
    adaptiveCoverCheck 10 (childLH (childLL (childHL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childHL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childHL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111123202 :
    adaptiveCoverCheck 10 (childHL (childLL (childHL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLL (childHL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childHL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111123203 :
    adaptiveCoverCheck 10 (childHH (childLL (childHL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLL (childHL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childHL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111123210 :
    adaptiveCoverCheck 10 (childLL (childLH (childHL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childHL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childHL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111123211 :
    adaptiveCoverCheck 10 (childLH (childLH (childHL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childHL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childHL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111123212 :
    adaptiveCoverCheck 10 (childHL (childLH (childHL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLH (childHL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childHL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111123213 :
    adaptiveCoverCheck 10 (childHH (childLH (childHL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLH (childHL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childHL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11112322 :
    adaptiveCoverCheck 11 (childHL (childHL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11112323 :
    adaptiveCoverCheck 11 (childHH (childHL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111123300 :
    adaptiveCoverCheck 10 (childLL (childLL (childHH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childHH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childHH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111123301 :
    adaptiveCoverCheck 10 (childLH (childLL (childHH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childHH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childHH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111123302 :
    adaptiveCoverCheck 10 (childHL (childLL (childHH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLL (childHH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childHH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111123303 :
    adaptiveCoverCheck 10 (childHH (childLL (childHH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLL (childHH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childHH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111123310 :
    adaptiveCoverCheck 10 (childLL (childLH (childHH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childHH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childHH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

end PartE
end GerverSofa
