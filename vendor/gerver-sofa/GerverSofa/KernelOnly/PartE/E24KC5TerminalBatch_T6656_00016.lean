import GerverSofa.KernelOnly.PartE.E24KC2ProofHelpers

/-! E24KC5 checkpoint-aware kernel batch. -/
noncomputable section

namespace GerverSofa
namespace PartE

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1023 :
    adaptiveCoverCheck 14 (childHH (childHL (childLL (childLH e24ThetaBelowRoot)))) = true := by
  have h : ((childHH (childHL (childLL (childLH e24ThetaBelowRoot))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 (childHH (childHL (childLL (childLH e24ThetaBelowRoot)))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1030 :
    adaptiveCoverCheck 14 (childLL (childHH (childLL (childLH e24ThetaBelowRoot)))) = true := by
  have h : ((childLL (childHH (childLL (childLH e24ThetaBelowRoot))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 (childLL (childHH (childLL (childLH e24ThetaBelowRoot)))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1031 :
    adaptiveCoverCheck 14 (childLH (childHH (childLL (childLH e24ThetaBelowRoot)))) = true := by
  have h : ((childLH (childHH (childLL (childLH e24ThetaBelowRoot))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 (childLH (childHH (childLL (childLH e24ThetaBelowRoot)))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1032 :
    adaptiveCoverCheck 14 (childHL (childHH (childLL (childLH e24ThetaBelowRoot)))) = true := by
  have h : ((childHL (childHH (childLL (childLH e24ThetaBelowRoot))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 (childHL (childHH (childLL (childLH e24ThetaBelowRoot)))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1033 :
    adaptiveCoverCheck 14 (childHH (childHH (childLL (childLH e24ThetaBelowRoot)))) = true := by
  have h : ((childHH (childHH (childLL (childLH e24ThetaBelowRoot))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 (childHH (childHH (childLL (childLH e24ThetaBelowRoot)))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110000 :
    adaptiveCoverCheck 12 (childLL (childLL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childLL (childLL (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110001 :
    adaptiveCoverCheck 12 (childLH (childLL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childLH (childLL (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1100020 :
    adaptiveCoverCheck 11 (childLL (childHL (childLL (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLL (childHL (childLL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHL (childLL (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1100021 :
    adaptiveCoverCheck 11 (childLH (childHL (childLL (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLH (childHL (childLL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHL (childLL (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1100022 :
    adaptiveCoverCheck 11 (childHL (childHL (childLL (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHL (childHL (childLL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childLL (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1100023 :
    adaptiveCoverCheck 11 (childHH (childHL (childLL (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHH (childHL (childLL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childLL (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1100030 :
    adaptiveCoverCheck 11 (childLL (childHH (childLL (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLL (childHH (childLL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHH (childLL (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1100031 :
    adaptiveCoverCheck 11 (childLH (childHH (childLL (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLH (childHH (childLL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHH (childLL (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11000320 :
    adaptiveCoverCheck 10 (childLL (childHL (childHH (childLL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLL (childHL (childHH (childLL (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHL (childHH (childLL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11000321 :
    adaptiveCoverCheck 10 (childLH (childHL (childHH (childLL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLH (childHL (childHH (childLL (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHL (childHH (childLL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11000322 :
    adaptiveCoverCheck 10 (childHL (childHL (childHH (childLL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHL (childHL (childHH (childLL (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childHH (childLL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11000323 :
    adaptiveCoverCheck 10 (childHH (childHL (childHH (childLL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHH (childHL (childHH (childLL (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childHH (childLL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11000330 :
    adaptiveCoverCheck 10 (childLL (childHH (childHH (childLL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLL (childHH (childHH (childLL (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHH (childHH (childLL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11000331 :
    adaptiveCoverCheck 10 (childLH (childHH (childHH (childLL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLH (childHH (childHH (childLL (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHH (childHH (childLL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11000332 :
    adaptiveCoverCheck 10 (childHL (childHH (childHH (childLL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHL (childHH (childHH (childLL (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childHH (childLL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11000333 :
    adaptiveCoverCheck 10 (childHH (childHH (childHH (childLL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHH (childHH (childHH (childLL (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childHH (childLL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110010 :
    adaptiveCoverCheck 12 (childLL (childLH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childLL (childLH (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110011 :
    adaptiveCoverCheck 12 (childLH (childLH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childLH (childLH (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1100120 :
    adaptiveCoverCheck 11 (childLL (childHL (childLH (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLL (childHL (childLH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHL (childLH (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1100121 :
    adaptiveCoverCheck 11 (childLH (childHL (childLH (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLH (childHL (childLH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHL (childLH (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11001220 :
    adaptiveCoverCheck 10 (childLL (childHL (childHL (childLH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLL (childHL (childHL (childLH (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHL (childHL (childLH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11001221 :
    adaptiveCoverCheck 10 (childLH (childHL (childHL (childLH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLH (childHL (childHL (childLH (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHL (childHL (childLH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11001222 :
    adaptiveCoverCheck 10 (childHL (childHL (childHL (childLH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHL (childHL (childHL (childLH (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childHL (childLH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11001223 :
    adaptiveCoverCheck 10 (childHH (childHL (childHL (childLH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHH (childHL (childHL (childLH (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childHL (childLH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11001230 :
    adaptiveCoverCheck 10 (childLL (childHH (childHL (childLH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLL (childHH (childHL (childLH (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHH (childHL (childLH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11001231 :
    adaptiveCoverCheck 10 (childLH (childHH (childHL (childLH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLH (childHH (childHL (childLH (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHH (childHL (childLH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11001232 :
    adaptiveCoverCheck 10 (childHL (childHH (childHL (childLH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHL (childHH (childHL (childLH (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childHL (childLH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11001233 :
    adaptiveCoverCheck 10 (childHH (childHH (childHL (childLH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHH (childHH (childHL (childLH (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childHL (childLH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1100130 :
    adaptiveCoverCheck 11 (childLL (childHH (childLH (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLL (childHH (childLH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHH (childLH (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1100131 :
    adaptiveCoverCheck 11 (childLH (childHH (childLH (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLH (childHH (childLH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHH (childLH (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11001320 :
    adaptiveCoverCheck 10 (childLL (childHL (childHH (childLH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLL (childHL (childHH (childLH (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHL (childHH (childLH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11001321 :
    adaptiveCoverCheck 10 (childLH (childHL (childHH (childLH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLH (childHL (childHH (childLH (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHL (childHH (childLH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11001322 :
    adaptiveCoverCheck 10 (childHL (childHL (childHH (childLH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHL (childHL (childHH (childLH (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childHH (childLH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11001323 :
    adaptiveCoverCheck 10 (childHH (childHL (childHH (childLH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHH (childHL (childHH (childLH (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childHH (childLH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11001330 :
    adaptiveCoverCheck 10 (childLL (childHH (childHH (childLH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLL (childHH (childHH (childLH (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHH (childHH (childLH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11001331 :
    adaptiveCoverCheck 10 (childLH (childHH (childHH (childLH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLH (childHH (childHH (childLH (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHH (childHH (childLH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11001332 :
    adaptiveCoverCheck 10 (childHL (childHH (childHH (childLH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHL (childHH (childHH (childLH (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childHH (childLH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11001333 :
    adaptiveCoverCheck 10 (childHH (childHH (childHH (childLH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHH (childHH (childHH (childLH (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childHH (childLH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11002000 :
    adaptiveCoverCheck 10 (childLL (childLL (childLL (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLL (childLL (childLL (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childLL (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11002001 :
    adaptiveCoverCheck 10 (childLH (childLL (childLL (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLH (childLL (childLL (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childLL (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11002002 :
    adaptiveCoverCheck 10 (childHL (childLL (childLL (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHL (childLL (childLL (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childLL (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11002003 :
    adaptiveCoverCheck 10 (childHH (childLL (childLL (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHH (childLL (childLL (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childLL (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11002010 :
    adaptiveCoverCheck 10 (childLL (childLH (childLL (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLL (childLH (childLL (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childLL (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11002011 :
    adaptiveCoverCheck 10 (childLH (childLH (childLL (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLH (childLH (childLL (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childLL (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11002012 :
    adaptiveCoverCheck 10 (childHL (childLH (childLL (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHL (childLH (childLL (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childLL (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11002013 :
    adaptiveCoverCheck 10 (childHH (childLH (childLL (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHH (childLH (childLL (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childLL (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11002020 :
    adaptiveCoverCheck 10 (childLL (childHL (childLL (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLL (childHL (childLL (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHL (childLL (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11002021 :
    adaptiveCoverCheck 10 (childLH (childHL (childLL (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLH (childHL (childLL (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHL (childLL (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11002022 :
    adaptiveCoverCheck 10 (childHL (childHL (childLL (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHL (childHL (childLL (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childLL (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11002023 :
    adaptiveCoverCheck 10 (childHH (childHL (childLL (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHH (childHL (childLL (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childLL (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11002030 :
    adaptiveCoverCheck 10 (childLL (childHH (childLL (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLL (childHH (childLL (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHH (childLL (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11002031 :
    adaptiveCoverCheck 10 (childLH (childHH (childLL (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLH (childHH (childLL (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHH (childLL (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11002032 :
    adaptiveCoverCheck 10 (childHL (childHH (childLL (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHL (childHH (childLL (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childLL (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11002033 :
    adaptiveCoverCheck 10 (childHH (childHH (childLL (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHH (childHH (childLL (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childLL (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11002100 :
    adaptiveCoverCheck 10 (childLL (childLL (childLH (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLL (childLL (childLH (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childLH (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11002101 :
    adaptiveCoverCheck 10 (childLH (childLL (childLH (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLH (childLL (childLH (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childLH (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11002102 :
    adaptiveCoverCheck 10 (childHL (childLL (childLH (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHL (childLL (childLH (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childLH (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11002103 :
    adaptiveCoverCheck 10 (childHH (childLL (childLH (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHH (childLL (childLH (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childLH (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11002110 :
    adaptiveCoverCheck 10 (childLL (childLH (childLH (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLL (childLH (childLH (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childLH (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11002111 :
    adaptiveCoverCheck 10 (childLH (childLH (childLH (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLH (childLH (childLH (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childLH (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11002112 :
    adaptiveCoverCheck 10 (childHL (childLH (childLH (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHL (childLH (childLH (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childLH (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11002113 :
    adaptiveCoverCheck 10 (childHH (childLH (childLH (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHH (childLH (childLH (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childLH (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11002120 :
    adaptiveCoverCheck 10 (childLL (childHL (childLH (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLL (childHL (childLH (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHL (childLH (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11002121 :
    adaptiveCoverCheck 10 (childLH (childHL (childLH (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLH (childHL (childLH (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHL (childLH (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11002122 :
    adaptiveCoverCheck 10 (childHL (childHL (childLH (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHL (childHL (childLH (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childLH (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11002123 :
    adaptiveCoverCheck 10 (childHH (childHL (childLH (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHH (childHL (childLH (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childLH (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11002130 :
    adaptiveCoverCheck 10 (childLL (childHH (childLH (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLL (childHH (childLH (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHH (childLH (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11002131 :
    adaptiveCoverCheck 10 (childLH (childHH (childLH (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLH (childHH (childLH (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHH (childLH (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11002132 :
    adaptiveCoverCheck 10 (childHL (childHH (childLH (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHL (childHH (childLH (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childLH (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11002133 :
    adaptiveCoverCheck 10 (childHH (childHH (childLH (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHH (childHH (childLH (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childLH (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1100220 :
    adaptiveCoverCheck 11 (childLL (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLL (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1100221 :
    adaptiveCoverCheck 11 (childLH (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLH (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1100222 :
    adaptiveCoverCheck 11 (childHL (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHL (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1100223 :
    adaptiveCoverCheck 11 (childHH (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHH (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1100230 :
    adaptiveCoverCheck 11 (childLL (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLL (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1100231 :
    adaptiveCoverCheck 11 (childLH (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLH (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1100232 :
    adaptiveCoverCheck 11 (childHL (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHL (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1100233 :
    adaptiveCoverCheck 11 (childHH (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHH (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childHL (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11003000 :
    adaptiveCoverCheck 10 (childLL (childLL (childLL (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLL (childLL (childLL (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childLL (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11003001 :
    adaptiveCoverCheck 10 (childLH (childLL (childLL (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLH (childLL (childLL (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childLL (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11003002 :
    adaptiveCoverCheck 10 (childHL (childLL (childLL (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHL (childLL (childLL (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childLL (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11003003 :
    adaptiveCoverCheck 10 (childHH (childLL (childLL (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHH (childLL (childLL (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childLL (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11003010 :
    adaptiveCoverCheck 10 (childLL (childLH (childLL (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLL (childLH (childLL (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childLL (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11003011 :
    adaptiveCoverCheck 10 (childLH (childLH (childLL (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLH (childLH (childLL (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childLL (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11003012 :
    adaptiveCoverCheck 10 (childHL (childLH (childLL (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHL (childLH (childLL (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childLL (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11003013 :
    adaptiveCoverCheck 10 (childHH (childLH (childLL (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHH (childLH (childLL (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childLL (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11003020 :
    adaptiveCoverCheck 10 (childLL (childHL (childLL (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLL (childHL (childLL (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHL (childLL (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11003021 :
    adaptiveCoverCheck 10 (childLH (childHL (childLL (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLH (childHL (childLL (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHL (childLL (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11003022 :
    adaptiveCoverCheck 10 (childHL (childHL (childLL (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHL (childHL (childLL (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childLL (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11003023 :
    adaptiveCoverCheck 10 (childHH (childHL (childLL (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHH (childHL (childLL (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childLL (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11003030 :
    adaptiveCoverCheck 10 (childLL (childHH (childLL (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLL (childHH (childLL (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHH (childLL (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11003031 :
    adaptiveCoverCheck 10 (childLH (childHH (childLL (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLH (childHH (childLL (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHH (childLL (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11003032 :
    adaptiveCoverCheck 10 (childHL (childHH (childLL (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHL (childHH (childLL (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childLL (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11003033 :
    adaptiveCoverCheck 10 (childHH (childHH (childLL (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHH (childHH (childLL (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childLL (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11003100 :
    adaptiveCoverCheck 10 (childLL (childLL (childLH (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLL (childLL (childLH (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childLH (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11003101 :
    adaptiveCoverCheck 10 (childLH (childLL (childLH (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLH (childLL (childLH (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childLH (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11003102 :
    adaptiveCoverCheck 10 (childHL (childLL (childLH (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHL (childLL (childLH (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childLH (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11003103 :
    adaptiveCoverCheck 10 (childHH (childLL (childLH (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHH (childLL (childLH (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childLH (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11003110 :
    adaptiveCoverCheck 10 (childLL (childLH (childLH (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLL (childLH (childLH (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childLH (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11003111 :
    adaptiveCoverCheck 10 (childLH (childLH (childLH (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLH (childLH (childLH (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childLH (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11003112 :
    adaptiveCoverCheck 10 (childHL (childLH (childLH (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHL (childLH (childLH (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childLH (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11003113 :
    adaptiveCoverCheck 10 (childHH (childLH (childLH (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHH (childLH (childLH (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childLH (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11003120 :
    adaptiveCoverCheck 10 (childLL (childHL (childLH (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLL (childHL (childLH (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHL (childLH (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11003121 :
    adaptiveCoverCheck 10 (childLH (childHL (childLH (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLH (childHL (childLH (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHL (childLH (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11003122 :
    adaptiveCoverCheck 10 (childHL (childHL (childLH (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHL (childHL (childLH (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childLH (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11003123 :
    adaptiveCoverCheck 10 (childHH (childHL (childLH (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHH (childHL (childLH (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childLH (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11003130 :
    adaptiveCoverCheck 10 (childLL (childHH (childLH (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLL (childHH (childLH (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHH (childLH (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11003131 :
    adaptiveCoverCheck 10 (childLH (childHH (childLH (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLH (childHH (childLH (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHH (childLH (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11003132 :
    adaptiveCoverCheck 10 (childHL (childHH (childLH (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHL (childHH (childLH (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childLH (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11003133 :
    adaptiveCoverCheck 10 (childHH (childHH (childLH (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHH (childHH (childLH (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childLH (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1100320 :
    adaptiveCoverCheck 11 (childLL (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLL (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1100321 :
    adaptiveCoverCheck 11 (childLH (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLH (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1100322 :
    adaptiveCoverCheck 11 (childHL (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHL (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1100323 :
    adaptiveCoverCheck 11 (childHH (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHH (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11003300 :
    adaptiveCoverCheck 10 (childLL (childLL (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLL (childLL (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11003301 :
    adaptiveCoverCheck 10 (childLH (childLL (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLH (childLL (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11003302 :
    adaptiveCoverCheck 10 (childHL (childLL (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHL (childLL (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11003303 :
    adaptiveCoverCheck 10 (childHH (childLL (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHH (childLL (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11003310 :
    adaptiveCoverCheck 10 (childLL (childLH (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLL (childLH (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11003311 :
    adaptiveCoverCheck 10 (childLH (childLH (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLH (childLH (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11003312 :
    adaptiveCoverCheck 10 (childHL (childLH (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHL (childLH (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11003313 :
    adaptiveCoverCheck 10 (childHH (childLH (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHH (childLH (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1100332 :
    adaptiveCoverCheck 11 (childHL (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHL (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1100333 :
    adaptiveCoverCheck 11 (childHH (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHH (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childHH (childLL (childLL (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110100 :
    adaptiveCoverCheck 12 (childLL (childLL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childLL (childLL (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110101 :
    adaptiveCoverCheck 12 (childLH (childLL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childLH (childLL (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1101020 :
    adaptiveCoverCheck 11 (childLL (childHL (childLL (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLL (childHL (childLL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHL (childLL (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1101021 :
    adaptiveCoverCheck 11 (childLH (childHL (childLL (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLH (childHL (childLL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHL (childLL (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11010220 :
    adaptiveCoverCheck 10 (childLL (childHL (childHL (childLL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLL (childHL (childHL (childLL (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHL (childHL (childLL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11010221 :
    adaptiveCoverCheck 10 (childLH (childHL (childHL (childLL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLH (childHL (childHL (childLL (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHL (childHL (childLL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11010222 :
    adaptiveCoverCheck 10 (childHL (childHL (childHL (childLL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHL (childHL (childHL (childLL (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childHL (childLL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11010223 :
    adaptiveCoverCheck 10 (childHH (childHL (childHL (childLL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHH (childHL (childHL (childLL (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childHL (childLL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11010230 :
    adaptiveCoverCheck 10 (childLL (childHH (childHL (childLL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLL (childHH (childHL (childLL (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHH (childHL (childLL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11010231 :
    adaptiveCoverCheck 10 (childLH (childHH (childHL (childLL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLH (childHH (childHL (childLL (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHH (childHL (childLL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11010232 :
    adaptiveCoverCheck 10 (childHL (childHH (childHL (childLL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHL (childHH (childHL (childLL (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childHL (childLL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11010233 :
    adaptiveCoverCheck 10 (childHH (childHH (childHL (childLL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHH (childHH (childHL (childLL (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childHL (childLL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1101030 :
    adaptiveCoverCheck 11 (childLL (childHH (childLL (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLL (childHH (childLL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHH (childLL (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1101031 :
    adaptiveCoverCheck 11 (childLH (childHH (childLL (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLH (childHH (childLL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHH (childLL (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1101032 :
    adaptiveCoverCheck 11 (childHL (childHH (childLL (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHL (childHH (childLL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childLL (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1101033 :
    adaptiveCoverCheck 11 (childHH (childHH (childLL (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHH (childHH (childLL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childLL (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110110 :
    adaptiveCoverCheck 12 (childLL (childLH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childLL (childLH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110111 :
    adaptiveCoverCheck 12 (childLH (childLH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childLH (childLH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1101120 :
    adaptiveCoverCheck 11 (childLL (childHL (childLH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLL (childHL (childLH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHL (childLH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1101121 :
    adaptiveCoverCheck 11 (childLH (childHL (childLH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLH (childHL (childLH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHL (childLH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1101122 :
    adaptiveCoverCheck 11 (childHL (childHL (childLH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHL (childHL (childLH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childLH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1101123 :
    adaptiveCoverCheck 11 (childHH (childHL (childLH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHH (childHL (childLH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childLH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1101130 :
    adaptiveCoverCheck 11 (childLL (childHH (childLH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLL (childHH (childLH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHH (childLH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1101131 :
    adaptiveCoverCheck 11 (childLH (childHH (childLH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLH (childHH (childLH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHH (childLH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1101132 :
    adaptiveCoverCheck 11 (childHL (childHH (childLH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHL (childHH (childLH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childLH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1101133 :
    adaptiveCoverCheck 11 (childHH (childHH (childLH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHH (childHH (childLH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childLH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11012000 :
    adaptiveCoverCheck 10 (childLL (childLL (childLL (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLL (childLL (childLL (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childLL (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11012001 :
    adaptiveCoverCheck 10 (childLH (childLL (childLL (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLH (childLL (childLL (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childLL (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11012002 :
    adaptiveCoverCheck 10 (childHL (childLL (childLL (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHL (childLL (childLL (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childLL (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11012003 :
    adaptiveCoverCheck 10 (childHH (childLL (childLL (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHH (childLL (childLL (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childLL (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11012010 :
    adaptiveCoverCheck 10 (childLL (childLH (childLL (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLL (childLH (childLL (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childLL (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11012011 :
    adaptiveCoverCheck 10 (childLH (childLH (childLL (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLH (childLH (childLL (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childLL (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11012012 :
    adaptiveCoverCheck 10 (childHL (childLH (childLL (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHL (childLH (childLL (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childLL (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11012013 :
    adaptiveCoverCheck 10 (childHH (childLH (childLL (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHH (childLH (childLL (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childLL (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11012020 :
    adaptiveCoverCheck 10 (childLL (childHL (childLL (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLL (childHL (childLL (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHL (childLL (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11012021 :
    adaptiveCoverCheck 10 (childLH (childHL (childLL (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLH (childHL (childLL (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHL (childLL (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11012022 :
    adaptiveCoverCheck 10 (childHL (childHL (childLL (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHL (childHL (childLL (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childLL (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11012023 :
    adaptiveCoverCheck 10 (childHH (childHL (childLL (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHH (childHL (childLL (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childLL (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11012030 :
    adaptiveCoverCheck 10 (childLL (childHH (childLL (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLL (childHH (childLL (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHH (childLL (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11012031 :
    adaptiveCoverCheck 10 (childLH (childHH (childLL (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLH (childHH (childLL (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHH (childLL (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11012032 :
    adaptiveCoverCheck 10 (childHL (childHH (childLL (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHL (childHH (childLL (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childLL (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11012033 :
    adaptiveCoverCheck 10 (childHH (childHH (childLL (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHH (childHH (childLL (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childLL (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11012100 :
    adaptiveCoverCheck 10 (childLL (childLL (childLH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLL (childLL (childLH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childLH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11012101 :
    adaptiveCoverCheck 10 (childLH (childLL (childLH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLH (childLL (childLH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childLH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11012102 :
    adaptiveCoverCheck 10 (childHL (childLL (childLH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHL (childLL (childLH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childLH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11012103 :
    adaptiveCoverCheck 10 (childHH (childLL (childLH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHH (childLL (childLH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childLH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11012110 :
    adaptiveCoverCheck 10 (childLL (childLH (childLH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLL (childLH (childLH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childLH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11012111 :
    adaptiveCoverCheck 10 (childLH (childLH (childLH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLH (childLH (childLH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childLH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11012112 :
    adaptiveCoverCheck 10 (childHL (childLH (childLH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHL (childLH (childLH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childLH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11012113 :
    adaptiveCoverCheck 10 (childHH (childLH (childLH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHH (childLH (childLH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childLH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11012120 :
    adaptiveCoverCheck 10 (childLL (childHL (childLH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLL (childHL (childLH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHL (childLH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11012121 :
    adaptiveCoverCheck 10 (childLH (childHL (childLH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLH (childHL (childLH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHL (childLH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11012122 :
    adaptiveCoverCheck 10 (childHL (childHL (childLH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHL (childHL (childLH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childLH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11012123 :
    adaptiveCoverCheck 10 (childHH (childHL (childLH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHH (childHL (childLH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childLH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11012130 :
    adaptiveCoverCheck 10 (childLL (childHH (childLH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLL (childHH (childLH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHH (childLH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11012131 :
    adaptiveCoverCheck 10 (childLH (childHH (childLH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLH (childHH (childLH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHH (childLH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110121320 :
    adaptiveCoverCheck 9 (childLL (childHL (childHH (childLH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLL (childHL (childHH (childLH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childHH (childLH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110121321 :
    adaptiveCoverCheck 9 (childLH (childHL (childHH (childLH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLH (childHL (childHH (childLH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childHH (childLH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110121322 :
    adaptiveCoverCheck 9 (childHL (childHL (childHH (childLH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHL (childHL (childHH (childLH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childHH (childLH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110121323 :
    adaptiveCoverCheck 9 (childHH (childHL (childHH (childLH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHH (childHL (childHH (childLH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childHH (childLH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110121330 :
    adaptiveCoverCheck 9 (childLL (childHH (childHH (childLH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLL (childHH (childHH (childLH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childHH (childLH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110121331 :
    adaptiveCoverCheck 9 (childLH (childHH (childHH (childLH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLH (childHH (childHH (childLH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childHH (childLH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110121332 :
    adaptiveCoverCheck 9 (childHL (childHH (childHH (childLH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHL (childHH (childHH (childLH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childHH (childLH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110121333 :
    adaptiveCoverCheck 9 (childHH (childHH (childHH (childLH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHH (childHH (childHH (childLH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childHH (childLH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11012200 :
    adaptiveCoverCheck 10 (childLL (childLL (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLL (childLL (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11012201 :
    adaptiveCoverCheck 10 (childLH (childLL (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLH (childLL (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11012202 :
    adaptiveCoverCheck 10 (childHL (childLL (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHL (childLL (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11012203 :
    adaptiveCoverCheck 10 (childHH (childLL (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHH (childLL (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11012210 :
    adaptiveCoverCheck 10 (childLL (childLH (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLL (childLH (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11012211 :
    adaptiveCoverCheck 10 (childLH (childLH (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLH (childLH (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11012212 :
    adaptiveCoverCheck 10 (childHL (childLH (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHL (childLH (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11012213 :
    adaptiveCoverCheck 10 (childHH (childLH (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHH (childLH (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1101222 :
    adaptiveCoverCheck 11 (childHL (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHL (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1101223 :
    adaptiveCoverCheck 11 (childHH (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHH (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11012300 :
    adaptiveCoverCheck 10 (childLL (childLL (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLL (childLL (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11012301 :
    adaptiveCoverCheck 10 (childLH (childLL (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLH (childLL (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11012302 :
    adaptiveCoverCheck 10 (childHL (childLL (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHL (childLL (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11012303 :
    adaptiveCoverCheck 10 (childHH (childLL (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHH (childLL (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11012310 :
    adaptiveCoverCheck 10 (childLL (childLH (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLL (childLH (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11012311 :
    adaptiveCoverCheck 10 (childLH (childLH (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLH (childLH (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11012312 :
    adaptiveCoverCheck 10 (childHL (childLH (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHL (childLH (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11012313 :
    adaptiveCoverCheck 10 (childHH (childLH (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHH (childLH (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1101232 :
    adaptiveCoverCheck 11 (childHL (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHL (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1101233 :
    adaptiveCoverCheck 11 (childHH (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHH (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childHL (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11013000 :
    adaptiveCoverCheck 10 (childLL (childLL (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLL (childLL (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11013001 :
    adaptiveCoverCheck 10 (childLH (childLL (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLH (childLL (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11013002 :
    adaptiveCoverCheck 10 (childHL (childLL (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHL (childLL (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11013003 :
    adaptiveCoverCheck 10 (childHH (childLL (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHH (childLL (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11013010 :
    adaptiveCoverCheck 10 (childLL (childLH (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLL (childLH (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11013011 :
    adaptiveCoverCheck 10 (childLH (childLH (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLH (childLH (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11013012 :
    adaptiveCoverCheck 10 (childHL (childLH (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHL (childLH (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110130130 :
    adaptiveCoverCheck 9 (childLL (childHH (childLH (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLL (childHH (childLH (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childLH (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110130131 :
    adaptiveCoverCheck 9 (childLH (childHH (childLH (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLH (childHH (childLH (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childLH (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110130132 :
    adaptiveCoverCheck 9 (childHL (childHH (childLH (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHL (childHH (childLH (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childLH (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110130133 :
    adaptiveCoverCheck 9 (childHH (childHH (childLH (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHH (childHH (childLH (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childLH (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11013020 :
    adaptiveCoverCheck 10 (childLL (childHL (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLL (childHL (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHL (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110130210 :
    adaptiveCoverCheck 9 (childLL (childLH (childHL (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLL (childLH (childHL (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHL (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110130211 :
    adaptiveCoverCheck 9 (childLH (childLH (childHL (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLH (childLH (childHL (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHL (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110130212 :
    adaptiveCoverCheck 9 (childHL (childLH (childHL (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHL (childLH (childHL (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHL (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110130213 :
    adaptiveCoverCheck 9 (childHH (childLH (childHL (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHH (childLH (childHL (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHL (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110130220 :
    adaptiveCoverCheck 9 (childLL (childHL (childHL (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLL (childHL (childHL (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childHL (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110130221 :
    adaptiveCoverCheck 9 (childLH (childHL (childHL (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLH (childHL (childHL (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childHL (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110130222 :
    adaptiveCoverCheck 9 (childHL (childHL (childHL (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHL (childHL (childHL (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childHL (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110130223 :
    adaptiveCoverCheck 9 (childHH (childHL (childHL (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHH (childHL (childHL (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childHL (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110130230 :
    adaptiveCoverCheck 9 (childLL (childHH (childHL (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLL (childHH (childHL (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childHL (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110130231 :
    adaptiveCoverCheck 9 (childLH (childHH (childHL (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLH (childHH (childHL (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childHL (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110130232 :
    adaptiveCoverCheck 9 (childHL (childHH (childHL (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHL (childHH (childHL (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childHL (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110130233 :
    adaptiveCoverCheck 9 (childHH (childHH (childHL (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHH (childHH (childHL (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childHL (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110130300 :
    adaptiveCoverCheck 9 (childLL (childLL (childHH (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLL (childLL (childHH (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHH (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110130301 :
    adaptiveCoverCheck 9 (childLH (childLL (childHH (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLH (childLL (childHH (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHH (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110130302 :
    adaptiveCoverCheck 9 (childHL (childLL (childHH (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHL (childLL (childHH (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHH (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110130303 :
    adaptiveCoverCheck 9 (childHH (childLL (childHH (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHH (childLL (childHH (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHH (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110130310 :
    adaptiveCoverCheck 9 (childLL (childLH (childHH (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLL (childLH (childHH (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHH (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110130311 :
    adaptiveCoverCheck 9 (childLH (childLH (childHH (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLH (childLH (childHH (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHH (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110130312 :
    adaptiveCoverCheck 9 (childHL (childLH (childHH (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHL (childLH (childHH (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHH (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110130313 :
    adaptiveCoverCheck 9 (childHH (childLH (childHH (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHH (childLH (childHH (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHH (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110130320 :
    adaptiveCoverCheck 9 (childLL (childHL (childHH (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLL (childHL (childHH (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childHH (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110130321 :
    adaptiveCoverCheck 9 (childLH (childHL (childHH (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLH (childHL (childHH (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childHH (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110130322 :
    adaptiveCoverCheck 9 (childHL (childHL (childHH (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHL (childHL (childHH (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childHH (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110130323 :
    adaptiveCoverCheck 9 (childHH (childHL (childHH (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHH (childHL (childHH (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childHH (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110130330 :
    adaptiveCoverCheck 9 (childLL (childHH (childHH (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLL (childHH (childHH (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childHH (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110130331 :
    adaptiveCoverCheck 9 (childLH (childHH (childHH (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLH (childHH (childHH (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childHH (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110130332 :
    adaptiveCoverCheck 9 (childHL (childHH (childHH (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHL (childHH (childHH (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childHH (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110130333 :
    adaptiveCoverCheck 9 (childHH (childHH (childHH (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHH (childHH (childHH (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childHH (childLL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11013100 :
    adaptiveCoverCheck 10 (childLL (childLL (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLL (childLL (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11013101 :
    adaptiveCoverCheck 10 (childLH (childLL (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLH (childLL (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110131020 :
    adaptiveCoverCheck 9 (childLL (childHL (childLL (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLL (childHL (childLL (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childLL (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110131021 :
    adaptiveCoverCheck 9 (childLH (childHL (childLL (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLH (childHL (childLL (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childLL (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110131022 :
    adaptiveCoverCheck 9 (childHL (childHL (childLL (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHL (childHL (childLL (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childLL (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110131023 :
    adaptiveCoverCheck 9 (childHH (childHL (childLL (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHH (childHL (childLL (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childLL (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110131030 :
    adaptiveCoverCheck 9 (childLL (childHH (childLL (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLL (childHH (childLL (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childLL (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110131031 :
    adaptiveCoverCheck 9 (childLH (childHH (childLL (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLH (childHH (childLL (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childLL (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110131032 :
    adaptiveCoverCheck 9 (childHL (childHH (childLL (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHL (childHH (childLL (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childLL (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110131033 :
    adaptiveCoverCheck 9 (childHH (childHH (childLL (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHH (childHH (childLL (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childLL (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11013110 :
    adaptiveCoverCheck 10 (childLL (childLH (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLL (childLH (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11013111 :
    adaptiveCoverCheck 10 (childLH (childLH (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLH (childLH (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110131120 :
    adaptiveCoverCheck 9 (childLL (childHL (childLH (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLL (childHL (childLH (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childLH (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110131121 :
    adaptiveCoverCheck 9 (childLH (childHL (childLH (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLH (childHL (childLH (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childLH (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110131122 :
    adaptiveCoverCheck 9 (childHL (childHL (childLH (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHL (childHL (childLH (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childLH (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110131123 :
    adaptiveCoverCheck 9 (childHH (childHL (childLH (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHH (childHL (childLH (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childLH (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110131130 :
    adaptiveCoverCheck 9 (childLL (childHH (childLH (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLL (childHH (childLH (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childLH (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110131131 :
    adaptiveCoverCheck 9 (childLH (childHH (childLH (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLH (childHH (childLH (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childLH (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110131132 :
    adaptiveCoverCheck 9 (childHL (childHH (childLH (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHL (childHH (childLH (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childLH (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110131133 :
    adaptiveCoverCheck 9 (childHH (childHH (childLH (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHH (childHH (childLH (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childLH (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110131200 :
    adaptiveCoverCheck 9 (childLL (childLL (childHL (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLL (childLL (childHL (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHL (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110131201 :
    adaptiveCoverCheck 9 (childLH (childLL (childHL (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLH (childLL (childHL (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHL (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110131202 :
    adaptiveCoverCheck 9 (childHL (childLL (childHL (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHL (childLL (childHL (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHL (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110131203 :
    adaptiveCoverCheck 9 (childHH (childLL (childHL (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHH (childLL (childHL (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHL (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110131210 :
    adaptiveCoverCheck 9 (childLL (childLH (childHL (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLL (childLH (childHL (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHL (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110131211 :
    adaptiveCoverCheck 9 (childLH (childLH (childHL (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLH (childLH (childHL (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHL (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110131212 :
    adaptiveCoverCheck 9 (childHL (childLH (childHL (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHL (childLH (childHL (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHL (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110131213 :
    adaptiveCoverCheck 9 (childHH (childLH (childHL (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHH (childLH (childHL (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHL (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110131220 :
    adaptiveCoverCheck 9 (childLL (childHL (childHL (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLL (childHL (childHL (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childHL (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110131221 :
    adaptiveCoverCheck 9 (childLH (childHL (childHL (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLH (childHL (childHL (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childHL (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110131222 :
    adaptiveCoverCheck 9 (childHL (childHL (childHL (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHL (childHL (childHL (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childHL (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110131223 :
    adaptiveCoverCheck 9 (childHH (childHL (childHL (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHH (childHL (childHL (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childHL (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110131230 :
    adaptiveCoverCheck 9 (childLL (childHH (childHL (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLL (childHH (childHL (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childHL (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110131231 :
    adaptiveCoverCheck 9 (childLH (childHH (childHL (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLH (childHH (childHL (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childHL (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110131232 :
    adaptiveCoverCheck 9 (childHL (childHH (childHL (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHL (childHH (childHL (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childHL (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110131233 :
    adaptiveCoverCheck 9 (childHH (childHH (childHL (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHH (childHH (childHL (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childHL (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110131300 :
    adaptiveCoverCheck 9 (childLL (childLL (childHH (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLL (childLL (childHH (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHH (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110131301 :
    adaptiveCoverCheck 9 (childLH (childLL (childHH (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLH (childLL (childHH (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHH (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110131302 :
    adaptiveCoverCheck 9 (childHL (childLL (childHH (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHL (childLL (childHH (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHH (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110131303 :
    adaptiveCoverCheck 9 (childHH (childLL (childHH (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHH (childLL (childHH (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHH (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110131310 :
    adaptiveCoverCheck 9 (childLL (childLH (childHH (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLL (childLH (childHH (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHH (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110131311 :
    adaptiveCoverCheck 9 (childLH (childLH (childHH (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLH (childLH (childHH (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHH (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110131312 :
    adaptiveCoverCheck 9 (childHL (childLH (childHH (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHL (childLH (childHH (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHH (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110131313 :
    adaptiveCoverCheck 9 (childHH (childLH (childHH (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHH (childLH (childHH (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHH (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110131320 :
    adaptiveCoverCheck 9 (childLL (childHL (childHH (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLL (childHL (childHH (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childHH (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110131321 :
    adaptiveCoverCheck 9 (childLH (childHL (childHH (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLH (childHL (childHH (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childHH (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110131322 :
    adaptiveCoverCheck 9 (childHL (childHL (childHH (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHL (childHL (childHH (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childHH (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110131323 :
    adaptiveCoverCheck 9 (childHH (childHL (childHH (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHH (childHL (childHH (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childHH (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110131330 :
    adaptiveCoverCheck 9 (childLL (childHH (childHH (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLL (childHH (childHH (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childHH (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110131331 :
    adaptiveCoverCheck 9 (childLH (childHH (childHH (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLH (childHH (childHH (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childHH (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110131332 :
    adaptiveCoverCheck 9 (childHL (childHH (childHH (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHL (childHH (childHH (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childHH (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110131333 :
    adaptiveCoverCheck 9 (childHH (childHH (childHH (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHH (childHH (childHH (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childHH (childLH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11013200 :
    adaptiveCoverCheck 10 (childLL (childLL (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLL (childLL (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11013201 :
    adaptiveCoverCheck 10 (childLH (childLL (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLH (childLL (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11013202 :
    adaptiveCoverCheck 10 (childHL (childLL (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHL (childLL (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11013203 :
    adaptiveCoverCheck 10 (childHH (childLL (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHH (childLL (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11013210 :
    adaptiveCoverCheck 10 (childLL (childLH (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLL (childLH (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11013211 :
    adaptiveCoverCheck 10 (childLH (childLH (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLH (childLH (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11013212 :
    adaptiveCoverCheck 10 (childHL (childLH (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHL (childLH (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11013213 :
    adaptiveCoverCheck 10 (childHH (childLH (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHH (childLH (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1101322 :
    adaptiveCoverCheck 11 (childHL (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHL (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1101323 :
    adaptiveCoverCheck 11 (childHH (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHH (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11013300 :
    adaptiveCoverCheck 10 (childLL (childLL (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLL (childLL (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11013301 :
    adaptiveCoverCheck 10 (childLH (childLL (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLH (childLL (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11013302 :
    adaptiveCoverCheck 10 (childHL (childLL (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHL (childLL (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11013303 :
    adaptiveCoverCheck 10 (childHH (childLL (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHH (childLL (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11013310 :
    adaptiveCoverCheck 10 (childLL (childLH (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLL (childLH (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11013311 :
    adaptiveCoverCheck 10 (childLH (childLH (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLH (childLH (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11013312 :
    adaptiveCoverCheck 10 (childHL (childLH (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHL (childLH (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11013313 :
    adaptiveCoverCheck 10 (childHH (childLH (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHH (childLH (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1101332 :
    adaptiveCoverCheck 11 (childHL (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHL (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1101333 :
    adaptiveCoverCheck 11 (childHH (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHH (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childHH (childLH (childLL (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110200 :
    adaptiveCoverCheck 12 (childLL (childLL (childHL (childLL (childLH (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childLL (childLL (childHL (childLL (childLH (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childHL (childLL (childLH (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110201 :
    adaptiveCoverCheck 12 (childLH (childLL (childHL (childLL (childLH (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childLH (childLL (childHL (childLL (childLH (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childHL (childLL (childLH (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110202 :
    adaptiveCoverCheck 12 (childHL (childLL (childHL (childLL (childLH (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childHL (childLL (childHL (childLL (childLH (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL (childHL (childLL (childLH (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110203 :
    adaptiveCoverCheck 12 (childHH (childLL (childHL (childLL (childLH (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childHH (childLL (childHL (childLL (childLH (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL (childHL (childLL (childLH (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110210 :
    adaptiveCoverCheck 12 (childLL (childLH (childHL (childLL (childLH (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childLL (childLH (childHL (childLL (childLH (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childHL (childLL (childLH (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110211 :
    adaptiveCoverCheck 12 (childLH (childLH (childHL (childLL (childLH (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childLH (childLH (childHL (childLL (childLH (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childHL (childLL (childLH (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110212 :
    adaptiveCoverCheck 12 (childHL (childLH (childHL (childLL (childLH (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childHL (childLH (childHL (childLL (childLH (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childHL (childLL (childLH (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110213 :
    adaptiveCoverCheck 12 (childHH (childLH (childHL (childLL (childLH (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childHH (childLH (childHL (childLL (childLH (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childHL (childLL (childLH (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11022 :
    adaptiveCoverCheck 13 (childHL (childHL (childLL (childLH (childLH e24ThetaBelowRoot))))) = true := by
  have h : ((childHL (childHL (childLL (childLH (childLH e24ThetaBelowRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childHL (childLL (childLH (childLH e24ThetaBelowRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11023 :
    adaptiveCoverCheck 13 (childHH (childHL (childLL (childLH (childLH e24ThetaBelowRoot))))) = true := by
  have h : ((childHH (childHL (childLL (childLH (childLH e24ThetaBelowRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childHL (childLL (childLH (childLH e24ThetaBelowRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110300 :
    adaptiveCoverCheck 12 (childLL (childLL (childHH (childLL (childLH (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childLL (childLL (childHH (childLL (childLH (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childHH (childLL (childLH (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110301 :
    adaptiveCoverCheck 12 (childLH (childLL (childHH (childLL (childLH (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childLH (childLL (childHH (childLL (childLH (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childHH (childLL (childLH (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110302 :
    adaptiveCoverCheck 12 (childHL (childLL (childHH (childLL (childLH (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childHL (childLL (childHH (childLL (childLH (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL (childHH (childLL (childLH (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110303 :
    adaptiveCoverCheck 12 (childHH (childLL (childHH (childLL (childLH (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childHH (childLL (childHH (childLL (childLH (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL (childHH (childLL (childLH (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110310 :
    adaptiveCoverCheck 12 (childLL (childLH (childHH (childLL (childLH (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childLL (childLH (childHH (childLL (childLH (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childHH (childLL (childLH (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110311 :
    adaptiveCoverCheck 12 (childLH (childLH (childHH (childLL (childLH (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childLH (childLH (childHH (childLL (childLH (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childHH (childLL (childLH (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110312 :
    adaptiveCoverCheck 12 (childHL (childLH (childHH (childLL (childLH (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childHL (childLH (childHH (childLL (childLH (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childHH (childLL (childLH (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf110313 :
    adaptiveCoverCheck 12 (childHH (childLH (childHH (childLL (childLH (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childHH (childLH (childHH (childLL (childLH (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childHH (childLL (childLH (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11032 :
    adaptiveCoverCheck 13 (childHL (childHH (childLL (childLH (childLH e24ThetaBelowRoot))))) = true := by
  have h : ((childHL (childHH (childLL (childLH (childLH e24ThetaBelowRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childHH (childLL (childLH (childLH e24ThetaBelowRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11033 :
    adaptiveCoverCheck 13 (childHH (childHH (childLL (childLH (childLH e24ThetaBelowRoot))))) = true := by
  have h : ((childHH (childHH (childLL (childLH (childLH e24ThetaBelowRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childHH (childLL (childLH (childLH e24ThetaBelowRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111000 :
    adaptiveCoverCheck 12 (childLL (childLL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childLL (childLL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111001 :
    adaptiveCoverCheck 12 (childLH (childLL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childLH (childLL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1110020 :
    adaptiveCoverCheck 11 (childLL (childHL (childLL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLL (childHL (childLL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHL (childLL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1110021 :
    adaptiveCoverCheck 11 (childLH (childHL (childLL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLH (childHL (childLL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHL (childLL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1110022 :
    adaptiveCoverCheck 11 (childHL (childHL (childLL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHL (childHL (childLL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childLL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1110023 :
    adaptiveCoverCheck 11 (childHH (childHL (childLL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHH (childHL (childLL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childLL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1110030 :
    adaptiveCoverCheck 11 (childLL (childHH (childLL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLL (childHH (childLL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHH (childLL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1110031 :
    adaptiveCoverCheck 11 (childLH (childHH (childLL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLH (childHH (childLL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHH (childLL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1110032 :
    adaptiveCoverCheck 11 (childHL (childHH (childLL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHL (childHH (childLL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childLL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1110033 :
    adaptiveCoverCheck 11 (childHH (childHH (childLL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHH (childHH (childLL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childLL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111010 :
    adaptiveCoverCheck 12 (childLL (childLH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childLL (childLH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111011 :
    adaptiveCoverCheck 12 (childLH (childLH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childLH (childLH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1110120 :
    adaptiveCoverCheck 11 (childLL (childHL (childLH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLL (childHL (childLH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHL (childLH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1110121 :
    adaptiveCoverCheck 11 (childLH (childHL (childLH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLH (childHL (childLH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHL (childLH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1110122 :
    adaptiveCoverCheck 11 (childHL (childHL (childLH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHL (childHL (childLH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childLH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1110123 :
    adaptiveCoverCheck 11 (childHH (childHL (childLH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHH (childHL (childLH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childLH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1110130 :
    adaptiveCoverCheck 11 (childLL (childHH (childLH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLL (childHH (childLH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHH (childLH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1110131 :
    adaptiveCoverCheck 11 (childLH (childHH (childLH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLH (childHH (childLH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHH (childLH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1110132 :
    adaptiveCoverCheck 11 (childHL (childHH (childLH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHL (childHH (childLH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childLH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1110133 :
    adaptiveCoverCheck 11 (childHH (childHH (childLH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHH (childHH (childLH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childLH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11102000 :
    adaptiveCoverCheck 10 (childLL (childLL (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLL (childLL (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11102001 :
    adaptiveCoverCheck 10 (childLH (childLL (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLH (childLL (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111020020 :
    adaptiveCoverCheck 9 (childLL (childHL (childLL (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLL (childHL (childLL (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childLL (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111020021 :
    adaptiveCoverCheck 9 (childLH (childHL (childLL (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLH (childHL (childLL (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childLL (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111020022 :
    adaptiveCoverCheck 9 (childHL (childHL (childLL (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHL (childHL (childLL (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childLL (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111020023 :
    adaptiveCoverCheck 9 (childHH (childHL (childLL (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHH (childHL (childLL (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childLL (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111020030 :
    adaptiveCoverCheck 9 (childLL (childHH (childLL (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLL (childHH (childLL (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childLL (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111020031 :
    adaptiveCoverCheck 9 (childLH (childHH (childLL (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLH (childHH (childLL (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childLL (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111020032 :
    adaptiveCoverCheck 9 (childHL (childHH (childLL (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHL (childHH (childLL (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childLL (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111020033 :
    adaptiveCoverCheck 9 (childHH (childHH (childLL (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHH (childHH (childLL (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childLL (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11102010 :
    adaptiveCoverCheck 10 (childLL (childLH (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLL (childLH (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11102011 :
    adaptiveCoverCheck 10 (childLH (childLH (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLH (childLH (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111020120 :
    adaptiveCoverCheck 9 (childLL (childHL (childLH (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLL (childHL (childLH (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childLH (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111020121 :
    adaptiveCoverCheck 9 (childLH (childHL (childLH (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLH (childHL (childLH (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childLH (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111020122 :
    adaptiveCoverCheck 9 (childHL (childHL (childLH (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHL (childHL (childLH (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childLH (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111020123 :
    adaptiveCoverCheck 9 (childHH (childHL (childLH (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHH (childHL (childLH (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childLH (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111020130 :
    adaptiveCoverCheck 9 (childLL (childHH (childLH (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLL (childHH (childLH (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childLH (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111020131 :
    adaptiveCoverCheck 9 (childLH (childHH (childLH (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLH (childHH (childLH (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childLH (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111020132 :
    adaptiveCoverCheck 9 (childHL (childHH (childLH (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHL (childHH (childLH (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childLH (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111020133 :
    adaptiveCoverCheck 9 (childHH (childHH (childLH (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHH (childHH (childLH (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childLH (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111020200 :
    adaptiveCoverCheck 9 (childLL (childLL (childHL (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLL (childLL (childHL (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHL (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111020201 :
    adaptiveCoverCheck 9 (childLH (childLL (childHL (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLH (childLL (childHL (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHL (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111020202 :
    adaptiveCoverCheck 9 (childHL (childLL (childHL (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHL (childLL (childHL (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHL (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111020203 :
    adaptiveCoverCheck 9 (childHH (childLL (childHL (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHH (childLL (childHL (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHL (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111020210 :
    adaptiveCoverCheck 9 (childLL (childLH (childHL (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLL (childLH (childHL (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHL (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111020211 :
    adaptiveCoverCheck 9 (childLH (childLH (childHL (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLH (childLH (childHL (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHL (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111020212 :
    adaptiveCoverCheck 9 (childHL (childLH (childHL (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHL (childLH (childHL (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHL (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111020213 :
    adaptiveCoverCheck 9 (childHH (childLH (childHL (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHH (childLH (childHL (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHL (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111020220 :
    adaptiveCoverCheck 9 (childLL (childHL (childHL (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLL (childHL (childHL (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childHL (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111020221 :
    adaptiveCoverCheck 9 (childLH (childHL (childHL (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLH (childHL (childHL (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childHL (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111020222 :
    adaptiveCoverCheck 9 (childHL (childHL (childHL (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHL (childHL (childHL (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childHL (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111020223 :
    adaptiveCoverCheck 9 (childHH (childHL (childHL (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHH (childHL (childHL (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childHL (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111020230 :
    adaptiveCoverCheck 9 (childLL (childHH (childHL (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLL (childHH (childHL (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childHL (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111020231 :
    adaptiveCoverCheck 9 (childLH (childHH (childHL (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLH (childHH (childHL (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childHL (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111020232 :
    adaptiveCoverCheck 9 (childHL (childHH (childHL (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHL (childHH (childHL (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childHL (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111020233 :
    adaptiveCoverCheck 9 (childHH (childHH (childHL (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHH (childHH (childHL (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childHL (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111020300 :
    adaptiveCoverCheck 9 (childLL (childLL (childHH (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLL (childLL (childHH (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHH (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111020301 :
    adaptiveCoverCheck 9 (childLH (childLL (childHH (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLH (childLL (childHH (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHH (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111020302 :
    adaptiveCoverCheck 9 (childHL (childLL (childHH (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHL (childLL (childHH (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHH (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111020303 :
    adaptiveCoverCheck 9 (childHH (childLL (childHH (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHH (childLL (childHH (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHH (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111020310 :
    adaptiveCoverCheck 9 (childLL (childLH (childHH (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLL (childLH (childHH (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHH (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111020311 :
    adaptiveCoverCheck 9 (childLH (childLH (childHH (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLH (childLH (childHH (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHH (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111020312 :
    adaptiveCoverCheck 9 (childHL (childLH (childHH (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHL (childLH (childHH (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHH (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111020313 :
    adaptiveCoverCheck 9 (childHH (childLH (childHH (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHH (childLH (childHH (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHH (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111020320 :
    adaptiveCoverCheck 9 (childLL (childHL (childHH (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLL (childHL (childHH (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childHH (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111020321 :
    adaptiveCoverCheck 9 (childLH (childHL (childHH (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLH (childHL (childHH (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childHH (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111020322 :
    adaptiveCoverCheck 9 (childHL (childHL (childHH (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHL (childHL (childHH (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childHH (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111020323 :
    adaptiveCoverCheck 9 (childHH (childHL (childHH (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHH (childHL (childHH (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childHH (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111020330 :
    adaptiveCoverCheck 9 (childLL (childHH (childHH (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLL (childHH (childHH (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childHH (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111020331 :
    adaptiveCoverCheck 9 (childLH (childHH (childHH (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLH (childHH (childHH (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childHH (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111020332 :
    adaptiveCoverCheck 9 (childHL (childHH (childHH (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHL (childHH (childHH (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childHH (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111020333 :
    adaptiveCoverCheck 9 (childHH (childHH (childHH (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHH (childHH (childHH (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childHH (childLL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11102100 :
    adaptiveCoverCheck 10 (childLL (childLL (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLL (childLL (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11102101 :
    adaptiveCoverCheck 10 (childLH (childLL (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLH (childLL (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11102102 :
    adaptiveCoverCheck 10 (childHL (childLL (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHL (childLL (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11102103 :
    adaptiveCoverCheck 10 (childHH (childLL (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHH (childLL (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11102110 :
    adaptiveCoverCheck 10 (childLL (childLH (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLL (childLH (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11102111 :
    adaptiveCoverCheck 10 (childLH (childLH (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLH (childLH (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11102112 :
    adaptiveCoverCheck 10 (childHL (childLH (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHL (childLH (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11102113 :
    adaptiveCoverCheck 10 (childHH (childLH (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHH (childLH (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111021200 :
    adaptiveCoverCheck 9 (childLL (childLL (childHL (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLL (childLL (childHL (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHL (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111021201 :
    adaptiveCoverCheck 9 (childLH (childLL (childHL (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLH (childLL (childHL (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHL (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111021202 :
    adaptiveCoverCheck 9 (childHL (childLL (childHL (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHL (childLL (childHL (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHL (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111021203 :
    adaptiveCoverCheck 9 (childHH (childLL (childHL (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHH (childLL (childHL (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHL (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111021210 :
    adaptiveCoverCheck 9 (childLL (childLH (childHL (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLL (childLH (childHL (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHL (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111021211 :
    adaptiveCoverCheck 9 (childLH (childLH (childHL (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLH (childLH (childHL (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHL (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111021212 :
    adaptiveCoverCheck 9 (childHL (childLH (childHL (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHL (childLH (childHL (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHL (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111021213 :
    adaptiveCoverCheck 9 (childHH (childLH (childHL (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHH (childLH (childHL (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHL (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111021220 :
    adaptiveCoverCheck 9 (childLL (childHL (childHL (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLL (childHL (childHL (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childHL (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111021221 :
    adaptiveCoverCheck 9 (childLH (childHL (childHL (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLH (childHL (childHL (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childHL (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111021222 :
    adaptiveCoverCheck 9 (childHL (childHL (childHL (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHL (childHL (childHL (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childHL (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111021223 :
    adaptiveCoverCheck 9 (childHH (childHL (childHL (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHH (childHL (childHL (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childHL (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111021230 :
    adaptiveCoverCheck 9 (childLL (childHH (childHL (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLL (childHH (childHL (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childHL (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111021231 :
    adaptiveCoverCheck 9 (childLH (childHH (childHL (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLH (childHH (childHL (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childHL (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111021232 :
    adaptiveCoverCheck 9 (childHL (childHH (childHL (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHL (childHH (childHL (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childHL (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111021233 :
    adaptiveCoverCheck 9 (childHH (childHH (childHL (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHH (childHH (childHL (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childHL (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111021300 :
    adaptiveCoverCheck 9 (childLL (childLL (childHH (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLL (childLL (childHH (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHH (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111021301 :
    adaptiveCoverCheck 9 (childLH (childLL (childHH (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLH (childLL (childHH (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHH (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111021302 :
    adaptiveCoverCheck 9 (childHL (childLL (childHH (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHL (childLL (childHH (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHH (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111021303 :
    adaptiveCoverCheck 9 (childHH (childLL (childHH (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHH (childLL (childHH (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHH (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111021310 :
    adaptiveCoverCheck 9 (childLL (childLH (childHH (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLL (childLH (childHH (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHH (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111021311 :
    adaptiveCoverCheck 9 (childLH (childLH (childHH (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLH (childLH (childHH (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHH (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111021312 :
    adaptiveCoverCheck 9 (childHL (childLH (childHH (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHL (childLH (childHH (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHH (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111021313 :
    adaptiveCoverCheck 9 (childHH (childLH (childHH (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHH (childLH (childHH (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHH (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111021320 :
    adaptiveCoverCheck 9 (childLL (childHL (childHH (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLL (childHL (childHH (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childHH (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111021321 :
    adaptiveCoverCheck 9 (childLH (childHL (childHH (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLH (childHL (childHH (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childHH (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111021322 :
    adaptiveCoverCheck 9 (childHL (childHL (childHH (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHL (childHL (childHH (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childHH (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111021323 :
    adaptiveCoverCheck 9 (childHH (childHL (childHH (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHH (childHL (childHH (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childHH (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111021330 :
    adaptiveCoverCheck 9 (childLL (childHH (childHH (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLL (childHH (childHH (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childHH (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111021331 :
    adaptiveCoverCheck 9 (childLH (childHH (childHH (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLH (childHH (childHH (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childHH (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111021332 :
    adaptiveCoverCheck 9 (childHL (childHH (childHH (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHL (childHH (childHH (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childHH (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111021333 :
    adaptiveCoverCheck 9 (childHH (childHH (childHH (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHH (childHH (childHH (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childHH (childLH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111022000 :
    adaptiveCoverCheck 9 (childLL (childLL (childLL (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLL (childLL (childLL (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childLL (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111022001 :
    adaptiveCoverCheck 9 (childLH (childLL (childLL (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLH (childLL (childLL (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childLL (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111022002 :
    adaptiveCoverCheck 9 (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111022003 :
    adaptiveCoverCheck 9 (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111022010 :
    adaptiveCoverCheck 9 (childLL (childLH (childLL (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLL (childLH (childLL (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childLL (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111022011 :
    adaptiveCoverCheck 9 (childLH (childLH (childLL (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLH (childLH (childLL (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childLL (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111022012 :
    adaptiveCoverCheck 9 (childHL (childLH (childLL (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHL (childLH (childLL (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childLL (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111022013 :
    adaptiveCoverCheck 9 (childHH (childLH (childLL (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHH (childLH (childLL (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childLL (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11102202 :
    adaptiveCoverCheck 10 (childHL (childLL (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHL (childLL (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11102203 :
    adaptiveCoverCheck 10 (childHH (childLL (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHH (childLL (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111022100 :
    adaptiveCoverCheck 9 (childLL (childLL (childLH (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLL (childLL (childLH (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childLH (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111022101 :
    adaptiveCoverCheck 9 (childLH (childLL (childLH (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLH (childLL (childLH (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childLH (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111022102 :
    adaptiveCoverCheck 9 (childHL (childLL (childLH (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHL (childLL (childLH (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childLH (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111022103 :
    adaptiveCoverCheck 9 (childHH (childLL (childLH (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHH (childLL (childLH (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childLH (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111022110 :
    adaptiveCoverCheck 9 (childLL (childLH (childLH (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLL (childLH (childLH (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childLH (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111022111 :
    adaptiveCoverCheck 9 (childLH (childLH (childLH (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLH (childLH (childLH (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childLH (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111022112 :
    adaptiveCoverCheck 9 (childHL (childLH (childLH (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHL (childLH (childLH (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childLH (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111022113 :
    adaptiveCoverCheck 9 (childHH (childLH (childLH (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHH (childLH (childLH (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childLH (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11102212 :
    adaptiveCoverCheck 10 (childHL (childLH (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHL (childLH (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11102213 :
    adaptiveCoverCheck 10 (childHH (childLH (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHH (childLH (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1110222 :
    adaptiveCoverCheck 11 (childHL (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHL (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1110223 :
    adaptiveCoverCheck 11 (childHH (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHH (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111023000 :
    adaptiveCoverCheck 9 (childLL (childLL (childLL (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLL (childLL (childLL (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childLL (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111023001 :
    adaptiveCoverCheck 9 (childLH (childLL (childLL (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLH (childLL (childLL (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childLL (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111023002 :
    adaptiveCoverCheck 9 (childHL (childLL (childLL (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHL (childLL (childLL (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childLL (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111023003 :
    adaptiveCoverCheck 9 (childHH (childLL (childLL (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHH (childLL (childLL (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childLL (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111023010 :
    adaptiveCoverCheck 9 (childLL (childLH (childLL (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLL (childLH (childLL (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childLL (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111023011 :
    adaptiveCoverCheck 9 (childLH (childLH (childLL (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLH (childLH (childLL (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childLL (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111023012 :
    adaptiveCoverCheck 9 (childHL (childLH (childLL (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHL (childLH (childLL (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childLL (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111023013 :
    adaptiveCoverCheck 9 (childHH (childLH (childLL (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHH (childLH (childLL (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childLL (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11102302 :
    adaptiveCoverCheck 10 (childHL (childLL (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHL (childLL (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11102303 :
    adaptiveCoverCheck 10 (childHH (childLL (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHH (childLL (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111023100 :
    adaptiveCoverCheck 9 (childLL (childLL (childLH (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLL (childLL (childLH (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childLH (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111023101 :
    adaptiveCoverCheck 9 (childLH (childLL (childLH (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLH (childLL (childLH (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childLH (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111023102 :
    adaptiveCoverCheck 9 (childHL (childLL (childLH (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHL (childLL (childLH (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childLH (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111023103 :
    adaptiveCoverCheck 9 (childHH (childLL (childLH (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHH (childLL (childLH (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childLH (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111023110 :
    adaptiveCoverCheck 9 (childLL (childLH (childLH (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLL (childLH (childLH (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childLH (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111023111 :
    adaptiveCoverCheck 9 (childLH (childLH (childLH (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLH (childLH (childLH (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childLH (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111023112 :
    adaptiveCoverCheck 9 (childHL (childLH (childLH (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHL (childLH (childLH (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childLH (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111023113 :
    adaptiveCoverCheck 9 (childHH (childLH (childLH (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHH (childLH (childLH (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childLH (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11102312 :
    adaptiveCoverCheck 10 (childHL (childLH (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHL (childLH (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11102313 :
    adaptiveCoverCheck 10 (childHH (childLH (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHH (childLH (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1110232 :
    adaptiveCoverCheck 11 (childHL (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHL (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1110233 :
    adaptiveCoverCheck 11 (childHH (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHH (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childHL (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11103000 :
    adaptiveCoverCheck 10 (childLL (childLL (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLL (childLL (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11103001 :
    adaptiveCoverCheck 10 (childLH (childLL (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLH (childLL (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11103002 :
    adaptiveCoverCheck 10 (childHL (childLL (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHL (childLL (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11103003 :
    adaptiveCoverCheck 10 (childHH (childLL (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHH (childLL (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11103010 :
    adaptiveCoverCheck 10 (childLL (childLH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLL (childLH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11103011 :
    adaptiveCoverCheck 10 (childLH (childLH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLH (childLH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11103012 :
    adaptiveCoverCheck 10 (childHL (childLH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHL (childLH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11103013 :
    adaptiveCoverCheck 10 (childHH (childLH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHH (childLH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111030200 :
    adaptiveCoverCheck 9 (childLL (childLL (childHL (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLL (childLL (childHL (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHL (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111030201 :
    adaptiveCoverCheck 9 (childLH (childLL (childHL (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLH (childLL (childHL (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHL (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111030202 :
    adaptiveCoverCheck 9 (childHL (childLL (childHL (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHL (childLL (childHL (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHL (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

end PartE
end GerverSofa
