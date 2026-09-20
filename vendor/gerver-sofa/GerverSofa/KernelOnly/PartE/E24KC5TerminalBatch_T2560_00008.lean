import GerverSofa.KernelOnly.PartE.E24KC2ProofHelpers

/-! E24KC5 checkpoint-aware kernel batch. -/
noncomputable section

namespace GerverSofa
namespace PartE

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010133010 :
    adaptiveCoverCheck 10 (childLL (childLH (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010133011 :
    adaptiveCoverCheck 10 (childLH (childLH (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101330120 :
    adaptiveCoverCheck 9 (childLL (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101330121 :
    adaptiveCoverCheck 9 (childLH (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101330122 :
    adaptiveCoverCheck 9 (childHL (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101330123 :
    adaptiveCoverCheck 9 (childHH (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childLH (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101330130 :
    adaptiveCoverCheck 9 (childLL (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101330131 :
    adaptiveCoverCheck 9 (childLH (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101330132 :
    adaptiveCoverCheck 9 (childHL (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101330133 :
    adaptiveCoverCheck 9 (childHH (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childLH (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101330200 :
    adaptiveCoverCheck 9 (childLL (childLL (childHL (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHL (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHL (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101330201 :
    adaptiveCoverCheck 9 (childLH (childLL (childHL (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHL (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHL (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101330202 :
    adaptiveCoverCheck 9 (childHL (childLL (childHL (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHL (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHL (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101330203 :
    adaptiveCoverCheck 9 (childHH (childLL (childHL (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHL (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHL (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101330210 :
    adaptiveCoverCheck 9 (childLL (childLH (childHL (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childHL (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHL (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101330211 :
    adaptiveCoverCheck 9 (childLH (childLH (childHL (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childHL (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHL (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101330212 :
    adaptiveCoverCheck 9 (childHL (childLH (childHL (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHL (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHL (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101330213 :
    adaptiveCoverCheck 9 (childHH (childLH (childHL (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHL (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHL (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101330220 :
    adaptiveCoverCheck 9 (childLL (childHL (childHL (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childHL (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childHL (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101330221 :
    adaptiveCoverCheck 9 (childLH (childHL (childHL (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childHL (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childHL (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101330222 :
    adaptiveCoverCheck 9 (childHL (childHL (childHL (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childHL (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childHL (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101330223 :
    adaptiveCoverCheck 9 (childHH (childHL (childHL (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childHL (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childHL (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101330230 :
    adaptiveCoverCheck 9 (childLL (childHH (childHL (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childHL (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childHL (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101330231 :
    adaptiveCoverCheck 9 (childLH (childHH (childHL (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childHL (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childHL (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101330232 :
    adaptiveCoverCheck 9 (childHL (childHH (childHL (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childHL (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childHL (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101330233 :
    adaptiveCoverCheck 9 (childHH (childHH (childHL (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childHL (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childHL (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101330300 :
    adaptiveCoverCheck 9 (childLL (childLL (childHH (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHH (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHH (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101330301 :
    adaptiveCoverCheck 9 (childLH (childLL (childHH (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHH (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHH (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101330302 :
    adaptiveCoverCheck 9 (childHL (childLL (childHH (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHH (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHH (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101330303 :
    adaptiveCoverCheck 9 (childHH (childLL (childHH (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHH (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHH (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101330310 :
    adaptiveCoverCheck 9 (childLL (childLH (childHH (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childHH (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHH (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101330311 :
    adaptiveCoverCheck 9 (childLH (childLH (childHH (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childHH (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHH (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101330312 :
    adaptiveCoverCheck 9 (childHL (childLH (childHH (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHH (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHH (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101330313 :
    adaptiveCoverCheck 9 (childHH (childLH (childHH (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHH (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHH (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101330320 :
    adaptiveCoverCheck 9 (childLL (childHL (childHH (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childHH (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childHH (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101330321 :
    adaptiveCoverCheck 9 (childLH (childHL (childHH (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childHH (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childHH (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101330322 :
    adaptiveCoverCheck 9 (childHL (childHL (childHH (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childHH (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childHH (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101330323 :
    adaptiveCoverCheck 9 (childHH (childHL (childHH (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childHH (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childHH (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101330330 :
    adaptiveCoverCheck 9 (childLL (childHH (childHH (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childHH (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childHH (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101330331 :
    adaptiveCoverCheck 9 (childLH (childHH (childHH (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childHH (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childHH (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101330332 :
    adaptiveCoverCheck 9 (childHL (childHH (childHH (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childHH (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childHH (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101330333 :
    adaptiveCoverCheck 9 (childHH (childHH (childHH (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childHH (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childHH (childLL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010133100 :
    adaptiveCoverCheck 10 (childLL (childLL (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010133101 :
    adaptiveCoverCheck 10 (childLH (childLL (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101331020 :
    adaptiveCoverCheck 9 (childLL (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101331021 :
    adaptiveCoverCheck 9 (childLH (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101331022 :
    adaptiveCoverCheck 9 (childHL (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101331023 :
    adaptiveCoverCheck 9 (childHH (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childLL (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101331030 :
    adaptiveCoverCheck 9 (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101331031 :
    adaptiveCoverCheck 9 (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101331032 :
    adaptiveCoverCheck 9 (childHL (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101331033 :
    adaptiveCoverCheck 9 (childHH (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childLL (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010133110 :
    adaptiveCoverCheck 10 (childLL (childLH (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010133111 :
    adaptiveCoverCheck 10 (childLH (childLH (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101331120 :
    adaptiveCoverCheck 9 (childLL (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101331121 :
    adaptiveCoverCheck 9 (childLH (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101331122 :
    adaptiveCoverCheck 9 (childHL (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101331123 :
    adaptiveCoverCheck 9 (childHH (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childLH (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101331130 :
    adaptiveCoverCheck 9 (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101331131 :
    adaptiveCoverCheck 9 (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101331132 :
    adaptiveCoverCheck 9 (childHL (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101331133 :
    adaptiveCoverCheck 9 (childHH (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childLH (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101331200 :
    adaptiveCoverCheck 9 (childLL (childLL (childHL (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHL (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHL (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101331201 :
    adaptiveCoverCheck 9 (childLH (childLL (childHL (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHL (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHL (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101331202 :
    adaptiveCoverCheck 9 (childHL (childLL (childHL (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHL (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHL (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101331203 :
    adaptiveCoverCheck 9 (childHH (childLL (childHL (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHL (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHL (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101331210 :
    adaptiveCoverCheck 9 (childLL (childLH (childHL (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childHL (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHL (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101331211 :
    adaptiveCoverCheck 9 (childLH (childLH (childHL (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childHL (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHL (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101331212 :
    adaptiveCoverCheck 9 (childHL (childLH (childHL (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHL (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHL (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101331213 :
    adaptiveCoverCheck 9 (childHH (childLH (childHL (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHL (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHL (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101331220 :
    adaptiveCoverCheck 9 (childLL (childHL (childHL (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childHL (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childHL (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101331221 :
    adaptiveCoverCheck 9 (childLH (childHL (childHL (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childHL (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childHL (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101331222 :
    adaptiveCoverCheck 9 (childHL (childHL (childHL (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childHL (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childHL (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101331223 :
    adaptiveCoverCheck 9 (childHH (childHL (childHL (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childHL (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childHL (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101331230 :
    adaptiveCoverCheck 9 (childLL (childHH (childHL (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childHL (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childHL (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101331231 :
    adaptiveCoverCheck 9 (childLH (childHH (childHL (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childHL (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childHL (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101331232 :
    adaptiveCoverCheck 9 (childHL (childHH (childHL (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childHL (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childHL (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101331233 :
    adaptiveCoverCheck 9 (childHH (childHH (childHL (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childHL (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childHL (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101331300 :
    adaptiveCoverCheck 9 (childLL (childLL (childHH (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHH (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHH (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101331301 :
    adaptiveCoverCheck 9 (childLH (childLL (childHH (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHH (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHH (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101331302 :
    adaptiveCoverCheck 9 (childHL (childLL (childHH (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHH (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHH (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101331303 :
    adaptiveCoverCheck 9 (childHH (childLL (childHH (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHH (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHH (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101331310 :
    adaptiveCoverCheck 9 (childLL (childLH (childHH (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childHH (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHH (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101331311 :
    adaptiveCoverCheck 9 (childLH (childLH (childHH (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childHH (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHH (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101331312 :
    adaptiveCoverCheck 9 (childHL (childLH (childHH (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHH (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHH (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101331313 :
    adaptiveCoverCheck 9 (childHH (childLH (childHH (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHH (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHH (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101331320 :
    adaptiveCoverCheck 9 (childLL (childHL (childHH (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childHH (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childHH (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101331321 :
    adaptiveCoverCheck 9 (childLH (childHL (childHH (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childHH (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childHH (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101331322 :
    adaptiveCoverCheck 9 (childHL (childHL (childHH (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childHH (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childHH (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101331323 :
    adaptiveCoverCheck 9 (childHH (childHL (childHH (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childHH (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childHH (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101331330 :
    adaptiveCoverCheck 9 (childLL (childHH (childHH (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childHH (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childHH (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101331331 :
    adaptiveCoverCheck 9 (childLH (childHH (childHH (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childHH (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childHH (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101331332 :
    adaptiveCoverCheck 9 (childHL (childHH (childHH (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childHH (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childHH (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0101331333 :
    adaptiveCoverCheck 9 (childHH (childHH (childHH (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childHH (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childHH (childLH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010133200 :
    adaptiveCoverCheck 10 (childLL (childLL (childHL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childHL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childHL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010133201 :
    adaptiveCoverCheck 10 (childLH (childLL (childHL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childHL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childHL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010133202 :
    adaptiveCoverCheck 10 (childHL (childLL (childHL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLL (childHL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childHL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010133203 :
    adaptiveCoverCheck 10 (childHH (childLL (childHL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLL (childHL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childHL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010133210 :
    adaptiveCoverCheck 10 (childLL (childLH (childHL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childHL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childHL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010133211 :
    adaptiveCoverCheck 10 (childLH (childLH (childHL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childHL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childHL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010133212 :
    adaptiveCoverCheck 10 (childHL (childLH (childHL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLH (childHL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childHL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010133213 :
    adaptiveCoverCheck 10 (childHH (childLH (childHL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLH (childHL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childHL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01013322 :
    adaptiveCoverCheck 11 (childHL (childHL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01013323 :
    adaptiveCoverCheck 11 (childHH (childHL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010133300 :
    adaptiveCoverCheck 10 (childLL (childLL (childHH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childHH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childHH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010133301 :
    adaptiveCoverCheck 10 (childLH (childLL (childHH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childHH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childHH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010133302 :
    adaptiveCoverCheck 10 (childHL (childLL (childHH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLL (childHH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childHH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010133303 :
    adaptiveCoverCheck 10 (childHH (childLL (childHH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLL (childHH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childHH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010133310 :
    adaptiveCoverCheck 10 (childLL (childLH (childHH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childHH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childHH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010133311 :
    adaptiveCoverCheck 10 (childLH (childLH (childHH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childHH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childHH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010133312 :
    adaptiveCoverCheck 10 (childHL (childLH (childHH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLH (childHH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childHH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010133313 :
    adaptiveCoverCheck 10 (childHH (childLH (childHH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLH (childHH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childHH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01013332 :
    adaptiveCoverCheck 11 (childHL (childHH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01013333 :
    adaptiveCoverCheck 11 (childHH (childHH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0102000 :
    adaptiveCoverCheck 12 (childLL (childLL (childLL (childHL (childLL (childLH (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childLL (childLL (childLL (childHL (childLL (childLH (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childLL (childHL (childLL (childLH (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0102001 :
    adaptiveCoverCheck 12 (childLH (childLL (childLL (childHL (childLL (childLH (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childLH (childLL (childLL (childHL (childLL (childLH (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childLL (childHL (childLL (childLH (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0102002 :
    adaptiveCoverCheck 12 (childHL (childLL (childLL (childHL (childLL (childLH (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childHL (childLL (childLL (childHL (childLL (childLH (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL (childLL (childHL (childLL (childLH (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0102003 :
    adaptiveCoverCheck 12 (childHH (childLL (childLL (childHL (childLL (childLH (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childHH (childLL (childLL (childHL (childLL (childLH (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL (childLL (childHL (childLL (childLH (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0102010 :
    adaptiveCoverCheck 12 (childLL (childLH (childLL (childHL (childLL (childLH (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childLL (childLH (childLL (childHL (childLL (childLH (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childLL (childHL (childLL (childLH (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0102011 :
    adaptiveCoverCheck 12 (childLH (childLH (childLL (childHL (childLL (childLH (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childLH (childLH (childLL (childHL (childLL (childLH (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childLL (childHL (childLL (childLH (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0102012 :
    adaptiveCoverCheck 12 (childHL (childLH (childLL (childHL (childLL (childLH (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childHL (childLH (childLL (childHL (childLL (childLH (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childLL (childHL (childLL (childLH (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0102013 :
    adaptiveCoverCheck 12 (childHH (childLH (childLL (childHL (childLL (childLH (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childHH (childLH (childLL (childHL (childLL (childLH (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childLL (childHL (childLL (childLH (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010202 :
    adaptiveCoverCheck 13 (childHL (childLL (childHL (childLL (childLH (childLL e24ThetaAboveRoot)))))) = true := by
  have h : ((childHL (childLL (childHL (childLL (childLH (childLL e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLL (childHL (childLL (childLH (childLL e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010203 :
    adaptiveCoverCheck 13 (childHH (childLL (childHL (childLL (childLH (childLL e24ThetaAboveRoot)))))) = true := by
  have h : ((childHH (childLL (childHL (childLL (childLH (childLL e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLL (childHL (childLL (childLH (childLL e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0102100 :
    adaptiveCoverCheck 12 (childLL (childLL (childLH (childHL (childLL (childLH (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childLL (childLL (childLH (childHL (childLL (childLH (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childLH (childHL (childLL (childLH (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0102101 :
    adaptiveCoverCheck 12 (childLH (childLL (childLH (childHL (childLL (childLH (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childLH (childLL (childLH (childHL (childLL (childLH (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childLH (childHL (childLL (childLH (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0102102 :
    adaptiveCoverCheck 12 (childHL (childLL (childLH (childHL (childLL (childLH (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childHL (childLL (childLH (childHL (childLL (childLH (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL (childLH (childHL (childLL (childLH (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0102103 :
    adaptiveCoverCheck 12 (childHH (childLL (childLH (childHL (childLL (childLH (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childHH (childLL (childLH (childHL (childLL (childLH (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL (childLH (childHL (childLL (childLH (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0102110 :
    adaptiveCoverCheck 12 (childLL (childLH (childLH (childHL (childLL (childLH (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childLL (childLH (childLH (childHL (childLL (childLH (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childLH (childHL (childLL (childLH (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0102111 :
    adaptiveCoverCheck 12 (childLH (childLH (childLH (childHL (childLL (childLH (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childLH (childLH (childLH (childHL (childLL (childLH (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childLH (childHL (childLL (childLH (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0102112 :
    adaptiveCoverCheck 12 (childHL (childLH (childLH (childHL (childLL (childLH (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childHL (childLH (childLH (childHL (childLL (childLH (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childLH (childHL (childLL (childLH (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0102113 :
    adaptiveCoverCheck 12 (childHH (childLH (childLH (childHL (childLL (childLH (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childHH (childLH (childLH (childHL (childLL (childLH (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childLH (childHL (childLL (childLH (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010212 :
    adaptiveCoverCheck 13 (childHL (childLH (childHL (childLL (childLH (childLL e24ThetaAboveRoot)))))) = true := by
  have h : ((childHL (childLH (childHL (childLL (childLH (childLL e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLH (childHL (childLL (childLH (childLL e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010213 :
    adaptiveCoverCheck 13 (childHH (childLH (childHL (childLL (childLH (childLL e24ThetaAboveRoot)))))) = true := by
  have h : ((childHH (childLH (childHL (childLL (childLH (childLL e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLH (childHL (childLL (childLH (childLL e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01022 :
    adaptiveCoverCheck 14 (childHL (childHL (childLL (childLH (childLL e24ThetaAboveRoot))))) = true := by
  have h : ((childHL (childHL (childLL (childLH (childLL e24ThetaAboveRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 (childHL (childHL (childLL (childLH (childLL e24ThetaAboveRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01023 :
    adaptiveCoverCheck 14 (childHH (childHL (childLL (childLH (childLL e24ThetaAboveRoot))))) = true := by
  have h : ((childHH (childHL (childLL (childLH (childLL e24ThetaAboveRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 (childHH (childHL (childLL (childLH (childLL e24ThetaAboveRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0103000 :
    adaptiveCoverCheck 12 (childLL (childLL (childLL (childHH (childLL (childLH (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childLL (childLL (childLL (childHH (childLL (childLH (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childLL (childHH (childLL (childLH (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0103001 :
    adaptiveCoverCheck 12 (childLH (childLL (childLL (childHH (childLL (childLH (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childLH (childLL (childLL (childHH (childLL (childLH (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childLL (childHH (childLL (childLH (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0103002 :
    adaptiveCoverCheck 12 (childHL (childLL (childLL (childHH (childLL (childLH (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childHL (childLL (childLL (childHH (childLL (childLH (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL (childLL (childHH (childLL (childLH (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0103003 :
    adaptiveCoverCheck 12 (childHH (childLL (childLL (childHH (childLL (childLH (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childHH (childLL (childLL (childHH (childLL (childLH (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL (childLL (childHH (childLL (childLH (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0103010 :
    adaptiveCoverCheck 12 (childLL (childLH (childLL (childHH (childLL (childLH (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childLL (childLH (childLL (childHH (childLL (childLH (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childLL (childHH (childLL (childLH (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0103011 :
    adaptiveCoverCheck 12 (childLH (childLH (childLL (childHH (childLL (childLH (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childLH (childLH (childLL (childHH (childLL (childLH (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childLL (childHH (childLL (childLH (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0103012 :
    adaptiveCoverCheck 12 (childHL (childLH (childLL (childHH (childLL (childLH (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childHL (childLH (childLL (childHH (childLL (childLH (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childLL (childHH (childLL (childLH (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0103013 :
    adaptiveCoverCheck 12 (childHH (childLH (childLL (childHH (childLL (childLH (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childHH (childLH (childLL (childHH (childLL (childLH (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childLL (childHH (childLL (childLH (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010302 :
    adaptiveCoverCheck 13 (childHL (childLL (childHH (childLL (childLH (childLL e24ThetaAboveRoot)))))) = true := by
  have h : ((childHL (childLL (childHH (childLL (childLH (childLL e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLL (childHH (childLL (childLH (childLL e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010303 :
    adaptiveCoverCheck 13 (childHH (childLL (childHH (childLL (childLH (childLL e24ThetaAboveRoot)))))) = true := by
  have h : ((childHH (childLL (childHH (childLL (childLH (childLL e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLL (childHH (childLL (childLH (childLL e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0103100 :
    adaptiveCoverCheck 12 (childLL (childLL (childLH (childHH (childLL (childLH (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childLL (childLL (childLH (childHH (childLL (childLH (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childLH (childHH (childLL (childLH (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0103101 :
    adaptiveCoverCheck 12 (childLH (childLL (childLH (childHH (childLL (childLH (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childLH (childLL (childLH (childHH (childLL (childLH (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childLH (childHH (childLL (childLH (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0103102 :
    adaptiveCoverCheck 12 (childHL (childLL (childLH (childHH (childLL (childLH (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childHL (childLL (childLH (childHH (childLL (childLH (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL (childLH (childHH (childLL (childLH (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0103103 :
    adaptiveCoverCheck 12 (childHH (childLL (childLH (childHH (childLL (childLH (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childHH (childLL (childLH (childHH (childLL (childLH (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL (childLH (childHH (childLL (childLH (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0103110 :
    adaptiveCoverCheck 12 (childLL (childLH (childLH (childHH (childLL (childLH (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childLL (childLH (childLH (childHH (childLL (childLH (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childLH (childHH (childLL (childLH (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0103111 :
    adaptiveCoverCheck 12 (childLH (childLH (childLH (childHH (childLL (childLH (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childLH (childLH (childLH (childHH (childLL (childLH (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childLH (childHH (childLL (childLH (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0103112 :
    adaptiveCoverCheck 12 (childHL (childLH (childLH (childHH (childLL (childLH (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childHL (childLH (childLH (childHH (childLL (childLH (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childLH (childHH (childLL (childLH (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0103113 :
    adaptiveCoverCheck 12 (childHH (childLH (childLH (childHH (childLL (childLH (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childHH (childLH (childLH (childHH (childLL (childLH (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childLH (childHH (childLL (childLH (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010312 :
    adaptiveCoverCheck 13 (childHL (childLH (childHH (childLL (childLH (childLL e24ThetaAboveRoot)))))) = true := by
  have h : ((childHL (childLH (childHH (childLL (childLH (childLL e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLH (childHH (childLL (childLH (childLL e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf010313 :
    adaptiveCoverCheck 13 (childHH (childLH (childHH (childLL (childLH (childLL e24ThetaAboveRoot)))))) = true := by
  have h : ((childHH (childLH (childHH (childLL (childLH (childLL e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLH (childHH (childLL (childLH (childLL e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01032 :
    adaptiveCoverCheck 14 (childHL (childHH (childLL (childLH (childLL e24ThetaAboveRoot))))) = true := by
  have h : ((childHL (childHH (childLL (childLH (childLL e24ThetaAboveRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 (childHL (childHH (childLL (childLH (childLL e24ThetaAboveRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01033 :
    adaptiveCoverCheck 14 (childHH (childHH (childLL (childLH (childLL e24ThetaAboveRoot))))) = true := by
  have h : ((childHH (childHH (childLL (childLH (childLL e24ThetaAboveRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 (childHH (childHH (childLL (childLH (childLL e24ThetaAboveRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011000 :
    adaptiveCoverCheck 13 (childLL (childLL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))) = true := by
  have h : ((childLL (childLL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL (childLL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011001 :
    adaptiveCoverCheck 13 (childLH (childLL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))) = true := by
  have h : ((childLH (childLL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH (childLL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011002 :
    adaptiveCoverCheck 13 (childHL (childLL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))) = true := by
  have h : ((childHL (childLL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011003 :
    adaptiveCoverCheck 13 (childHH (childLL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))) = true := by
  have h : ((childHH (childLL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011010 :
    adaptiveCoverCheck 13 (childLL (childLH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))) = true := by
  have h : ((childLL (childLH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL (childLH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011011 :
    adaptiveCoverCheck 13 (childLH (childLH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))) = true := by
  have h : ((childLH (childLH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH (childLH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011012 :
    adaptiveCoverCheck 13 (childHL (childLH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))) = true := by
  have h : ((childHL (childLH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011013 :
    adaptiveCoverCheck 13 (childHH (childLH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))) = true := by
  have h : ((childHH (childLH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110200 :
    adaptiveCoverCheck 12 (childLL (childLL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childLL (childLL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110201 :
    adaptiveCoverCheck 12 (childLH (childLL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childLH (childLL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01102020 :
    adaptiveCoverCheck 11 (childLL (childHL (childLL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childHL (childLL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHL (childLL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01102021 :
    adaptiveCoverCheck 11 (childLH (childHL (childLL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childHL (childLL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHL (childLL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01102022 :
    adaptiveCoverCheck 11 (childHL (childHL (childLL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHL (childLL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childLL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01102023 :
    adaptiveCoverCheck 11 (childHH (childHL (childLL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHL (childLL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childLL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01102030 :
    adaptiveCoverCheck 11 (childLL (childHH (childLL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childHH (childLL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHH (childLL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01102031 :
    adaptiveCoverCheck 11 (childLH (childHH (childLL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childHH (childLL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHH (childLL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01102032 :
    adaptiveCoverCheck 11 (childHL (childHH (childLL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHH (childLL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childLL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01102033 :
    adaptiveCoverCheck 11 (childHH (childHH (childLL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHH (childLL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childLL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110210 :
    adaptiveCoverCheck 12 (childLL (childLH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childLL (childLH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110211 :
    adaptiveCoverCheck 12 (childLH (childLH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childLH (childLH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01102120 :
    adaptiveCoverCheck 11 (childLL (childHL (childLH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childHL (childLH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHL (childLH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01102121 :
    adaptiveCoverCheck 11 (childLH (childHL (childLH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childHL (childLH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHL (childLH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01102122 :
    adaptiveCoverCheck 11 (childHL (childHL (childLH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHL (childLH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childLH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01102123 :
    adaptiveCoverCheck 11 (childHH (childHL (childLH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHL (childLH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childLH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01102130 :
    adaptiveCoverCheck 11 (childLL (childHH (childLH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childHH (childLH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHH (childLH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01102131 :
    adaptiveCoverCheck 11 (childLH (childHH (childLH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childHH (childLH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHH (childLH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01102132 :
    adaptiveCoverCheck 11 (childHL (childHH (childLH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHH (childLH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childLH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01102133 :
    adaptiveCoverCheck 11 (childHH (childHH (childLH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHH (childLH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childLH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011022000 :
    adaptiveCoverCheck 10 (childLL (childLL (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011022001 :
    adaptiveCoverCheck 10 (childLH (childLL (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110220020 :
    adaptiveCoverCheck 9 (childLL (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110220021 :
    adaptiveCoverCheck 9 (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110220022 :
    adaptiveCoverCheck 9 (childHL (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110220023 :
    adaptiveCoverCheck 9 (childHH (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childLL (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110220030 :
    adaptiveCoverCheck 9 (childLL (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110220031 :
    adaptiveCoverCheck 9 (childLH (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110220032 :
    adaptiveCoverCheck 9 (childHL (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110220033 :
    adaptiveCoverCheck 9 (childHH (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childLL (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011022010 :
    adaptiveCoverCheck 10 (childLL (childLH (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011022011 :
    adaptiveCoverCheck 10 (childLH (childLH (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110220120 :
    adaptiveCoverCheck 9 (childLL (childHL (childLH (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childLH (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childLH (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110220121 :
    adaptiveCoverCheck 9 (childLH (childHL (childLH (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childLH (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childLH (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110220122 :
    adaptiveCoverCheck 9 (childHL (childHL (childLH (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childLH (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childLH (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110220123 :
    adaptiveCoverCheck 9 (childHH (childHL (childLH (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childLH (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childLH (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110220130 :
    adaptiveCoverCheck 9 (childLL (childHH (childLH (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childLH (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childLH (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110220131 :
    adaptiveCoverCheck 9 (childLH (childHH (childLH (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childLH (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childLH (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110220132 :
    adaptiveCoverCheck 9 (childHL (childHH (childLH (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childLH (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childLH (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110220133 :
    adaptiveCoverCheck 9 (childHH (childHH (childLH (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childLH (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childLH (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110220200 :
    adaptiveCoverCheck 9 (childLL (childLL (childHL (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHL (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHL (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110220201 :
    adaptiveCoverCheck 9 (childLH (childLL (childHL (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHL (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHL (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110220202 :
    adaptiveCoverCheck 9 (childHL (childLL (childHL (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHL (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHL (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110220203 :
    adaptiveCoverCheck 9 (childHH (childLL (childHL (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHL (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHL (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110220210 :
    adaptiveCoverCheck 9 (childLL (childLH (childHL (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childHL (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHL (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110220211 :
    adaptiveCoverCheck 9 (childLH (childLH (childHL (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childHL (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHL (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110220212 :
    adaptiveCoverCheck 9 (childHL (childLH (childHL (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHL (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHL (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110220213 :
    adaptiveCoverCheck 9 (childHH (childLH (childHL (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHL (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHL (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110220220 :
    adaptiveCoverCheck 9 (childLL (childHL (childHL (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childHL (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childHL (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110220221 :
    adaptiveCoverCheck 9 (childLH (childHL (childHL (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childHL (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childHL (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110220222 :
    adaptiveCoverCheck 9 (childHL (childHL (childHL (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childHL (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childHL (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110220223 :
    adaptiveCoverCheck 9 (childHH (childHL (childHL (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childHL (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childHL (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110220230 :
    adaptiveCoverCheck 9 (childLL (childHH (childHL (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childHL (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childHL (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110220231 :
    adaptiveCoverCheck 9 (childLH (childHH (childHL (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childHL (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childHL (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110220232 :
    adaptiveCoverCheck 9 (childHL (childHH (childHL (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childHL (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childHL (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110220233 :
    adaptiveCoverCheck 9 (childHH (childHH (childHL (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childHL (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childHL (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110220300 :
    adaptiveCoverCheck 9 (childLL (childLL (childHH (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHH (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHH (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110220301 :
    adaptiveCoverCheck 9 (childLH (childLL (childHH (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHH (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHH (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110220302 :
    adaptiveCoverCheck 9 (childHL (childLL (childHH (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHH (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHH (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110220303 :
    adaptiveCoverCheck 9 (childHH (childLL (childHH (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHH (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHH (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110220310 :
    adaptiveCoverCheck 9 (childLL (childLH (childHH (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childHH (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHH (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110220311 :
    adaptiveCoverCheck 9 (childLH (childLH (childHH (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childHH (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHH (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110220312 :
    adaptiveCoverCheck 9 (childHL (childLH (childHH (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHH (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHH (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110220313 :
    adaptiveCoverCheck 9 (childHH (childLH (childHH (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHH (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHH (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110220320 :
    adaptiveCoverCheck 9 (childLL (childHL (childHH (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childHH (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childHH (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110220321 :
    adaptiveCoverCheck 9 (childLH (childHL (childHH (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childHH (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childHH (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110220322 :
    adaptiveCoverCheck 9 (childHL (childHL (childHH (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childHH (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childHH (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110220323 :
    adaptiveCoverCheck 9 (childHH (childHL (childHH (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childHH (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childHH (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110220330 :
    adaptiveCoverCheck 9 (childLL (childHH (childHH (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childHH (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childHH (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110220331 :
    adaptiveCoverCheck 9 (childLH (childHH (childHH (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childHH (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childHH (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110220332 :
    adaptiveCoverCheck 9 (childHL (childHH (childHH (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childHH (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childHH (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110220333 :
    adaptiveCoverCheck 9 (childHH (childHH (childHH (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childHH (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childHH (childLL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011022100 :
    adaptiveCoverCheck 10 (childLL (childLL (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011022101 :
    adaptiveCoverCheck 10 (childLH (childLL (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110221020 :
    adaptiveCoverCheck 9 (childLL (childHL (childLL (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childLL (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childLL (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110221021 :
    adaptiveCoverCheck 9 (childLH (childHL (childLL (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childLL (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childLL (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110221022 :
    adaptiveCoverCheck 9 (childHL (childHL (childLL (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childLL (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childLL (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110221023 :
    adaptiveCoverCheck 9 (childHH (childHL (childLL (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childLL (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childLL (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110221030 :
    adaptiveCoverCheck 9 (childLL (childHH (childLL (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childLL (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childLL (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110221031 :
    adaptiveCoverCheck 9 (childLH (childHH (childLL (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childLL (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childLL (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110221032 :
    adaptiveCoverCheck 9 (childHL (childHH (childLL (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childLL (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childLL (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110221033 :
    adaptiveCoverCheck 9 (childHH (childHH (childLL (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childLL (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childLL (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011022110 :
    adaptiveCoverCheck 10 (childLL (childLH (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011022111 :
    adaptiveCoverCheck 10 (childLH (childLH (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110221120 :
    adaptiveCoverCheck 9 (childLL (childHL (childLH (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childLH (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childLH (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110221121 :
    adaptiveCoverCheck 9 (childLH (childHL (childLH (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childLH (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childLH (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110221122 :
    adaptiveCoverCheck 9 (childHL (childHL (childLH (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childLH (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childLH (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110221123 :
    adaptiveCoverCheck 9 (childHH (childHL (childLH (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childLH (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childLH (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110221130 :
    adaptiveCoverCheck 9 (childLL (childHH (childLH (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childLH (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childLH (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110221131 :
    adaptiveCoverCheck 9 (childLH (childHH (childLH (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childLH (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childLH (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110221132 :
    adaptiveCoverCheck 9 (childHL (childHH (childLH (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childLH (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childLH (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110221133 :
    adaptiveCoverCheck 9 (childHH (childHH (childLH (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childLH (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childLH (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110221200 :
    adaptiveCoverCheck 9 (childLL (childLL (childHL (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHL (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHL (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110221201 :
    adaptiveCoverCheck 9 (childLH (childLL (childHL (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHL (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHL (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110221202 :
    adaptiveCoverCheck 9 (childHL (childLL (childHL (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHL (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHL (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110221203 :
    adaptiveCoverCheck 9 (childHH (childLL (childHL (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHL (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHL (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110221210 :
    adaptiveCoverCheck 9 (childLL (childLH (childHL (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childHL (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHL (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110221211 :
    adaptiveCoverCheck 9 (childLH (childLH (childHL (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childHL (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHL (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110221212 :
    adaptiveCoverCheck 9 (childHL (childLH (childHL (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHL (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHL (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110221213 :
    adaptiveCoverCheck 9 (childHH (childLH (childHL (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHL (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHL (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110221220 :
    adaptiveCoverCheck 9 (childLL (childHL (childHL (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childHL (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childHL (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110221221 :
    adaptiveCoverCheck 9 (childLH (childHL (childHL (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childHL (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childHL (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110221222 :
    adaptiveCoverCheck 9 (childHL (childHL (childHL (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childHL (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childHL (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110221223 :
    adaptiveCoverCheck 9 (childHH (childHL (childHL (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childHL (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childHL (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110221230 :
    adaptiveCoverCheck 9 (childLL (childHH (childHL (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childHL (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childHL (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110221231 :
    adaptiveCoverCheck 9 (childLH (childHH (childHL (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childHL (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childHL (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110221232 :
    adaptiveCoverCheck 9 (childHL (childHH (childHL (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childHL (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childHL (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110221233 :
    adaptiveCoverCheck 9 (childHH (childHH (childHL (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childHL (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childHL (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110221300 :
    adaptiveCoverCheck 9 (childLL (childLL (childHH (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHH (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHH (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110221301 :
    adaptiveCoverCheck 9 (childLH (childLL (childHH (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHH (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHH (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110221302 :
    adaptiveCoverCheck 9 (childHL (childLL (childHH (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHH (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHH (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110221303 :
    adaptiveCoverCheck 9 (childHH (childLL (childHH (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHH (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHH (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110221310 :
    adaptiveCoverCheck 9 (childLL (childLH (childHH (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childHH (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHH (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110221311 :
    adaptiveCoverCheck 9 (childLH (childLH (childHH (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childHH (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHH (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110221312 :
    adaptiveCoverCheck 9 (childHL (childLH (childHH (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHH (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHH (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110221313 :
    adaptiveCoverCheck 9 (childHH (childLH (childHH (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHH (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHH (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110221320 :
    adaptiveCoverCheck 9 (childLL (childHL (childHH (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childHH (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childHH (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110221321 :
    adaptiveCoverCheck 9 (childLH (childHL (childHH (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childHH (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childHH (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110221322 :
    adaptiveCoverCheck 9 (childHL (childHL (childHH (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childHH (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childHH (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110221323 :
    adaptiveCoverCheck 9 (childHH (childHL (childHH (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childHH (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childHH (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110221330 :
    adaptiveCoverCheck 9 (childLL (childHH (childHH (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childHH (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childHH (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110221331 :
    adaptiveCoverCheck 9 (childLH (childHH (childHH (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childHH (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childHH (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110221332 :
    adaptiveCoverCheck 9 (childHL (childHH (childHH (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childHH (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childHH (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110221333 :
    adaptiveCoverCheck 9 (childHH (childHH (childHH (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childHH (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childHH (childLH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011022200 :
    adaptiveCoverCheck 10 (childLL (childLL (childHL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childHL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childHL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011022201 :
    adaptiveCoverCheck 10 (childLH (childLL (childHL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childHL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childHL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011022202 :
    adaptiveCoverCheck 10 (childHL (childLL (childHL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLL (childHL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childHL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011022203 :
    adaptiveCoverCheck 10 (childHH (childLL (childHL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLL (childHL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childHL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011022210 :
    adaptiveCoverCheck 10 (childLL (childLH (childHL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childHL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childHL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011022211 :
    adaptiveCoverCheck 10 (childLH (childLH (childHL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childHL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childHL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011022212 :
    adaptiveCoverCheck 10 (childHL (childLH (childHL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLH (childHL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childHL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011022213 :
    adaptiveCoverCheck 10 (childHH (childLH (childHL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLH (childHL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childHL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01102222 :
    adaptiveCoverCheck 11 (childHL (childHL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01102223 :
    adaptiveCoverCheck 11 (childHH (childHL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011022300 :
    adaptiveCoverCheck 10 (childLL (childLL (childHH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childHH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childHH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011022301 :
    adaptiveCoverCheck 10 (childLH (childLL (childHH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childHH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childHH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011022302 :
    adaptiveCoverCheck 10 (childHL (childLL (childHH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLL (childHH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childHH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011022303 :
    adaptiveCoverCheck 10 (childHH (childLL (childHH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLL (childHH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childHH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011022310 :
    adaptiveCoverCheck 10 (childLL (childLH (childHH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childHH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childHH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011022311 :
    adaptiveCoverCheck 10 (childLH (childLH (childHH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childHH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childHH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011022312 :
    adaptiveCoverCheck 10 (childHL (childLH (childHH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLH (childHH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childHH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011022313 :
    adaptiveCoverCheck 10 (childHH (childLH (childHH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLH (childHH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childHH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01102232 :
    adaptiveCoverCheck 11 (childHL (childHH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01102233 :
    adaptiveCoverCheck 11 (childHH (childHH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011023000 :
    adaptiveCoverCheck 10 (childLL (childLL (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011023001 :
    adaptiveCoverCheck 10 (childLH (childLL (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110230020 :
    adaptiveCoverCheck 9 (childLL (childHL (childLL (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childLL (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childLL (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110230021 :
    adaptiveCoverCheck 9 (childLH (childHL (childLL (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childLL (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childLL (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110230022 :
    adaptiveCoverCheck 9 (childHL (childHL (childLL (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childLL (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childLL (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110230023 :
    adaptiveCoverCheck 9 (childHH (childHL (childLL (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childLL (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childLL (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110230030 :
    adaptiveCoverCheck 9 (childLL (childHH (childLL (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childLL (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childLL (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110230031 :
    adaptiveCoverCheck 9 (childLH (childHH (childLL (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childLL (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childLL (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110230032 :
    adaptiveCoverCheck 9 (childHL (childHH (childLL (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childLL (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childLL (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110230033 :
    adaptiveCoverCheck 9 (childHH (childHH (childLL (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childLL (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childLL (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011023010 :
    adaptiveCoverCheck 10 (childLL (childLH (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011023011 :
    adaptiveCoverCheck 10 (childLH (childLH (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110230120 :
    adaptiveCoverCheck 9 (childLL (childHL (childLH (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childLH (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childLH (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110230121 :
    adaptiveCoverCheck 9 (childLH (childHL (childLH (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childLH (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childLH (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110230122 :
    adaptiveCoverCheck 9 (childHL (childHL (childLH (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childLH (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childLH (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110230123 :
    adaptiveCoverCheck 9 (childHH (childHL (childLH (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childLH (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childLH (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110230130 :
    adaptiveCoverCheck 9 (childLL (childHH (childLH (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childLH (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childLH (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110230131 :
    adaptiveCoverCheck 9 (childLH (childHH (childLH (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childLH (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childLH (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110230132 :
    adaptiveCoverCheck 9 (childHL (childHH (childLH (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childLH (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childLH (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110230133 :
    adaptiveCoverCheck 9 (childHH (childHH (childLH (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childLH (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childLH (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110230200 :
    adaptiveCoverCheck 9 (childLL (childLL (childHL (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHL (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHL (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110230201 :
    adaptiveCoverCheck 9 (childLH (childLL (childHL (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHL (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHL (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110230202 :
    adaptiveCoverCheck 9 (childHL (childLL (childHL (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHL (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHL (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110230203 :
    adaptiveCoverCheck 9 (childHH (childLL (childHL (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHL (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHL (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110230210 :
    adaptiveCoverCheck 9 (childLL (childLH (childHL (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childHL (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHL (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110230211 :
    adaptiveCoverCheck 9 (childLH (childLH (childHL (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childHL (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHL (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110230212 :
    adaptiveCoverCheck 9 (childHL (childLH (childHL (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHL (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHL (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110230213 :
    adaptiveCoverCheck 9 (childHH (childLH (childHL (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHL (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHL (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110230220 :
    adaptiveCoverCheck 9 (childLL (childHL (childHL (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childHL (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childHL (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110230221 :
    adaptiveCoverCheck 9 (childLH (childHL (childHL (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childHL (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childHL (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110230222 :
    adaptiveCoverCheck 9 (childHL (childHL (childHL (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childHL (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childHL (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110230223 :
    adaptiveCoverCheck 9 (childHH (childHL (childHL (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childHL (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childHL (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110230230 :
    adaptiveCoverCheck 9 (childLL (childHH (childHL (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childHL (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childHL (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110230231 :
    adaptiveCoverCheck 9 (childLH (childHH (childHL (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childHL (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childHL (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110230232 :
    adaptiveCoverCheck 9 (childHL (childHH (childHL (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childHL (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childHL (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110230233 :
    adaptiveCoverCheck 9 (childHH (childHH (childHL (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childHL (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childHL (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110230300 :
    adaptiveCoverCheck 9 (childLL (childLL (childHH (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHH (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHH (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110230301 :
    adaptiveCoverCheck 9 (childLH (childLL (childHH (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHH (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHH (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110230302 :
    adaptiveCoverCheck 9 (childHL (childLL (childHH (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHH (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHH (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110230303 :
    adaptiveCoverCheck 9 (childHH (childLL (childHH (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHH (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHH (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110230310 :
    adaptiveCoverCheck 9 (childLL (childLH (childHH (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childHH (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHH (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110230311 :
    adaptiveCoverCheck 9 (childLH (childLH (childHH (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childHH (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHH (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110230312 :
    adaptiveCoverCheck 9 (childHL (childLH (childHH (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHH (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHH (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110230313 :
    adaptiveCoverCheck 9 (childHH (childLH (childHH (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHH (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHH (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110230320 :
    adaptiveCoverCheck 9 (childLL (childHL (childHH (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childHH (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childHH (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110230321 :
    adaptiveCoverCheck 9 (childLH (childHL (childHH (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childHH (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childHH (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110230322 :
    adaptiveCoverCheck 9 (childHL (childHL (childHH (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childHH (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childHH (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110230323 :
    adaptiveCoverCheck 9 (childHH (childHL (childHH (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childHH (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childHH (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110230330 :
    adaptiveCoverCheck 9 (childLL (childHH (childHH (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childHH (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childHH (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110230331 :
    adaptiveCoverCheck 9 (childLH (childHH (childHH (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childHH (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childHH (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110230332 :
    adaptiveCoverCheck 9 (childHL (childHH (childHH (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childHH (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childHH (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110230333 :
    adaptiveCoverCheck 9 (childHH (childHH (childHH (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childHH (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childHH (childLL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011023100 :
    adaptiveCoverCheck 10 (childLL (childLL (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011023101 :
    adaptiveCoverCheck 10 (childLH (childLL (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110231020 :
    adaptiveCoverCheck 9 (childLL (childHL (childLL (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childLL (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childLL (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110231021 :
    adaptiveCoverCheck 9 (childLH (childHL (childLL (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childLL (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childLL (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110231022 :
    adaptiveCoverCheck 9 (childHL (childHL (childLL (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childLL (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childLL (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110231023 :
    adaptiveCoverCheck 9 (childHH (childHL (childLL (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childLL (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childLL (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110231030 :
    adaptiveCoverCheck 9 (childLL (childHH (childLL (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childLL (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childLL (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110231031 :
    adaptiveCoverCheck 9 (childLH (childHH (childLL (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childLL (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childLL (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110231032 :
    adaptiveCoverCheck 9 (childHL (childHH (childLL (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childLL (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childLL (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110231033 :
    adaptiveCoverCheck 9 (childHH (childHH (childLL (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childLL (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childLL (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011023110 :
    adaptiveCoverCheck 10 (childLL (childLH (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011023111 :
    adaptiveCoverCheck 10 (childLH (childLH (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110231120 :
    adaptiveCoverCheck 9 (childLL (childHL (childLH (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childLH (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childLH (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110231121 :
    adaptiveCoverCheck 9 (childLH (childHL (childLH (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childLH (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childLH (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110231122 :
    adaptiveCoverCheck 9 (childHL (childHL (childLH (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childLH (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childLH (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110231123 :
    adaptiveCoverCheck 9 (childHH (childHL (childLH (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childLH (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childLH (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110231130 :
    adaptiveCoverCheck 9 (childLL (childHH (childLH (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childLH (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childLH (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110231131 :
    adaptiveCoverCheck 9 (childLH (childHH (childLH (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childLH (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childLH (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110231132 :
    adaptiveCoverCheck 9 (childHL (childHH (childLH (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childLH (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childLH (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110231133 :
    adaptiveCoverCheck 9 (childHH (childHH (childLH (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childLH (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childLH (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110231200 :
    adaptiveCoverCheck 9 (childLL (childLL (childHL (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHL (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHL (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110231201 :
    adaptiveCoverCheck 9 (childLH (childLL (childHL (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHL (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHL (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110231202 :
    adaptiveCoverCheck 9 (childHL (childLL (childHL (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHL (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHL (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110231203 :
    adaptiveCoverCheck 9 (childHH (childLL (childHL (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHL (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHL (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110231210 :
    adaptiveCoverCheck 9 (childLL (childLH (childHL (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childHL (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHL (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110231211 :
    adaptiveCoverCheck 9 (childLH (childLH (childHL (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childHL (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHL (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110231212 :
    adaptiveCoverCheck 9 (childHL (childLH (childHL (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHL (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHL (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110231213 :
    adaptiveCoverCheck 9 (childHH (childLH (childHL (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHL (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHL (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110231220 :
    adaptiveCoverCheck 9 (childLL (childHL (childHL (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childHL (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childHL (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110231221 :
    adaptiveCoverCheck 9 (childLH (childHL (childHL (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childHL (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childHL (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110231222 :
    adaptiveCoverCheck 9 (childHL (childHL (childHL (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childHL (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childHL (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110231223 :
    adaptiveCoverCheck 9 (childHH (childHL (childHL (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childHL (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childHL (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110231230 :
    adaptiveCoverCheck 9 (childLL (childHH (childHL (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childHL (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childHL (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110231231 :
    adaptiveCoverCheck 9 (childLH (childHH (childHL (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childHL (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childHL (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110231232 :
    adaptiveCoverCheck 9 (childHL (childHH (childHL (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childHL (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childHL (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110231233 :
    adaptiveCoverCheck 9 (childHH (childHH (childHL (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childHL (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childHL (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110231300 :
    adaptiveCoverCheck 9 (childLL (childLL (childHH (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHH (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHH (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110231301 :
    adaptiveCoverCheck 9 (childLH (childLL (childHH (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHH (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHH (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110231302 :
    adaptiveCoverCheck 9 (childHL (childLL (childHH (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHH (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHH (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110231303 :
    adaptiveCoverCheck 9 (childHH (childLL (childHH (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHH (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHH (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110231310 :
    adaptiveCoverCheck 9 (childLL (childLH (childHH (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childHH (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHH (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110231311 :
    adaptiveCoverCheck 9 (childLH (childLH (childHH (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childHH (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHH (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110231312 :
    adaptiveCoverCheck 9 (childHL (childLH (childHH (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHH (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHH (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110231313 :
    adaptiveCoverCheck 9 (childHH (childLH (childHH (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHH (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHH (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110231320 :
    adaptiveCoverCheck 9 (childLL (childHL (childHH (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childHH (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childHH (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110231321 :
    adaptiveCoverCheck 9 (childLH (childHL (childHH (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childHH (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childHH (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110231322 :
    adaptiveCoverCheck 9 (childHL (childHL (childHH (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childHH (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childHH (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110231323 :
    adaptiveCoverCheck 9 (childHH (childHL (childHH (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childHH (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childHH (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110231330 :
    adaptiveCoverCheck 9 (childLL (childHH (childHH (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childHH (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childHH (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110231331 :
    adaptiveCoverCheck 9 (childLH (childHH (childHH (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childHH (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childHH (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110231332 :
    adaptiveCoverCheck 9 (childHL (childHH (childHH (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childHH (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childHH (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110231333 :
    adaptiveCoverCheck 9 (childHH (childHH (childHH (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childHH (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childHH (childLH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011023200 :
    adaptiveCoverCheck 10 (childLL (childLL (childHL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childHL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childHL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011023201 :
    adaptiveCoverCheck 10 (childLH (childLL (childHL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childHL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childHL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011023202 :
    adaptiveCoverCheck 10 (childHL (childLL (childHL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLL (childHL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childHL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011023203 :
    adaptiveCoverCheck 10 (childHH (childLL (childHL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLL (childHL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childHL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011023210 :
    adaptiveCoverCheck 10 (childLL (childLH (childHL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childHL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childHL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011023211 :
    adaptiveCoverCheck 10 (childLH (childLH (childHL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childHL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childHL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011023212 :
    adaptiveCoverCheck 10 (childHL (childLH (childHL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLH (childHL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childHL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011023213 :
    adaptiveCoverCheck 10 (childHH (childLH (childHL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLH (childHL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childHL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01102322 :
    adaptiveCoverCheck 11 (childHL (childHL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01102323 :
    adaptiveCoverCheck 11 (childHH (childHL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011023300 :
    adaptiveCoverCheck 10 (childLL (childLL (childHH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childHH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childHH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011023301 :
    adaptiveCoverCheck 10 (childLH (childLL (childHH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childHH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childHH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011023302 :
    adaptiveCoverCheck 10 (childHL (childLL (childHH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLL (childHH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childHH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011023303 :
    adaptiveCoverCheck 10 (childHH (childLL (childHH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLL (childHH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childHH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011023310 :
    adaptiveCoverCheck 10 (childLL (childLH (childHH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childHH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childHH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011023311 :
    adaptiveCoverCheck 10 (childLH (childLH (childHH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childHH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childHH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011023312 :
    adaptiveCoverCheck 10 (childHL (childLH (childHH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLH (childHH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childHH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011023313 :
    adaptiveCoverCheck 10 (childHH (childLH (childHH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLH (childHH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childHH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01102332 :
    adaptiveCoverCheck 11 (childHL (childHH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01102333 :
    adaptiveCoverCheck 11 (childHH (childHH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110300 :
    adaptiveCoverCheck 12 (childLL (childLL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childLL (childLL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110301 :
    adaptiveCoverCheck 12 (childLH (childLL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childLH (childLL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01103020 :
    adaptiveCoverCheck 11 (childLL (childHL (childLL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childHL (childLL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHL (childLL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01103021 :
    adaptiveCoverCheck 11 (childLH (childHL (childLL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childHL (childLL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHL (childLL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01103022 :
    adaptiveCoverCheck 11 (childHL (childHL (childLL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHL (childLL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childLL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01103023 :
    adaptiveCoverCheck 11 (childHH (childHL (childLL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHL (childLL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childLL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01103030 :
    adaptiveCoverCheck 11 (childLL (childHH (childLL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childHH (childLL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHH (childLL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01103031 :
    adaptiveCoverCheck 11 (childLH (childHH (childLL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childHH (childLL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHH (childLL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01103032 :
    adaptiveCoverCheck 11 (childHL (childHH (childLL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHH (childLL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childLL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01103033 :
    adaptiveCoverCheck 11 (childHH (childHH (childLL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHH (childLL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childLL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110310 :
    adaptiveCoverCheck 12 (childLL (childLH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childLL (childLH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110311 :
    adaptiveCoverCheck 12 (childLH (childLH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childLH (childLH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01103120 :
    adaptiveCoverCheck 11 (childLL (childHL (childLH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childHL (childLH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHL (childLH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01103121 :
    adaptiveCoverCheck 11 (childLH (childHL (childLH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childHL (childLH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHL (childLH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01103122 :
    adaptiveCoverCheck 11 (childHL (childHL (childLH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHL (childLH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childLH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01103123 :
    adaptiveCoverCheck 11 (childHH (childHL (childLH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHL (childLH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childLH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01103130 :
    adaptiveCoverCheck 11 (childLL (childHH (childLH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childHH (childLH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHH (childLH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01103131 :
    adaptiveCoverCheck 11 (childLH (childHH (childLH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childHH (childLH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHH (childLH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01103132 :
    adaptiveCoverCheck 11 (childHL (childHH (childLH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHH (childLH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childLH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01103133 :
    adaptiveCoverCheck 11 (childHH (childHH (childLH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHH (childLH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childLH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011032000 :
    adaptiveCoverCheck 10 (childLL (childLL (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011032001 :
    adaptiveCoverCheck 10 (childLH (childLL (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110320020 :
    adaptiveCoverCheck 9 (childLL (childHL (childLL (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childLL (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childLL (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110320021 :
    adaptiveCoverCheck 9 (childLH (childHL (childLL (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childLL (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childLL (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110320022 :
    adaptiveCoverCheck 9 (childHL (childHL (childLL (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childLL (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childLL (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110320023 :
    adaptiveCoverCheck 9 (childHH (childHL (childLL (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childLL (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childLL (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110320030 :
    adaptiveCoverCheck 9 (childLL (childHH (childLL (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childLL (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childLL (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110320031 :
    adaptiveCoverCheck 9 (childLH (childHH (childLL (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childLL (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childLL (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110320032 :
    adaptiveCoverCheck 9 (childHL (childHH (childLL (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childLL (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childLL (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110320033 :
    adaptiveCoverCheck 9 (childHH (childHH (childLL (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childLL (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childLL (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011032010 :
    adaptiveCoverCheck 10 (childLL (childLH (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011032011 :
    adaptiveCoverCheck 10 (childLH (childLH (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110320120 :
    adaptiveCoverCheck 9 (childLL (childHL (childLH (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childLH (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childLH (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110320121 :
    adaptiveCoverCheck 9 (childLH (childHL (childLH (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childLH (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childLH (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110320122 :
    adaptiveCoverCheck 9 (childHL (childHL (childLH (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childLH (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childLH (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110320123 :
    adaptiveCoverCheck 9 (childHH (childHL (childLH (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childLH (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childLH (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110320130 :
    adaptiveCoverCheck 9 (childLL (childHH (childLH (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childLH (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childLH (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110320131 :
    adaptiveCoverCheck 9 (childLH (childHH (childLH (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childLH (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childLH (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110320132 :
    adaptiveCoverCheck 9 (childHL (childHH (childLH (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childLH (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childLH (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110320133 :
    adaptiveCoverCheck 9 (childHH (childHH (childLH (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childLH (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childLH (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110320200 :
    adaptiveCoverCheck 9 (childLL (childLL (childHL (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHL (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHL (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110320201 :
    adaptiveCoverCheck 9 (childLH (childLL (childHL (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHL (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHL (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110320202 :
    adaptiveCoverCheck 9 (childHL (childLL (childHL (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHL (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHL (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110320203 :
    adaptiveCoverCheck 9 (childHH (childLL (childHL (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHL (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHL (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110320210 :
    adaptiveCoverCheck 9 (childLL (childLH (childHL (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childHL (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHL (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110320211 :
    adaptiveCoverCheck 9 (childLH (childLH (childHL (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childHL (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHL (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110320212 :
    adaptiveCoverCheck 9 (childHL (childLH (childHL (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHL (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHL (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110320213 :
    adaptiveCoverCheck 9 (childHH (childLH (childHL (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHL (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHL (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110320220 :
    adaptiveCoverCheck 9 (childLL (childHL (childHL (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childHL (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childHL (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110320221 :
    adaptiveCoverCheck 9 (childLH (childHL (childHL (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childHL (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childHL (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110320222 :
    adaptiveCoverCheck 9 (childHL (childHL (childHL (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childHL (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childHL (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110320223 :
    adaptiveCoverCheck 9 (childHH (childHL (childHL (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childHL (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childHL (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110320230 :
    adaptiveCoverCheck 9 (childLL (childHH (childHL (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childHL (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childHL (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110320231 :
    adaptiveCoverCheck 9 (childLH (childHH (childHL (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childHL (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childHL (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110320232 :
    adaptiveCoverCheck 9 (childHL (childHH (childHL (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childHL (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childHL (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110320233 :
    adaptiveCoverCheck 9 (childHH (childHH (childHL (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childHL (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childHL (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110320300 :
    adaptiveCoverCheck 9 (childLL (childLL (childHH (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHH (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHH (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110320301 :
    adaptiveCoverCheck 9 (childLH (childLL (childHH (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHH (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHH (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110320302 :
    adaptiveCoverCheck 9 (childHL (childLL (childHH (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHH (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHH (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110320303 :
    adaptiveCoverCheck 9 (childHH (childLL (childHH (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHH (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHH (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110320310 :
    adaptiveCoverCheck 9 (childLL (childLH (childHH (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childHH (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHH (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110320311 :
    adaptiveCoverCheck 9 (childLH (childLH (childHH (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childHH (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHH (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110320312 :
    adaptiveCoverCheck 9 (childHL (childLH (childHH (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHH (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHH (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110320313 :
    adaptiveCoverCheck 9 (childHH (childLH (childHH (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHH (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHH (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110320320 :
    adaptiveCoverCheck 9 (childLL (childHL (childHH (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childHH (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childHH (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110320321 :
    adaptiveCoverCheck 9 (childLH (childHL (childHH (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childHH (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childHH (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110320322 :
    adaptiveCoverCheck 9 (childHL (childHL (childHH (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childHH (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childHH (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110320323 :
    adaptiveCoverCheck 9 (childHH (childHL (childHH (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childHH (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childHH (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110320330 :
    adaptiveCoverCheck 9 (childLL (childHH (childHH (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childHH (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childHH (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110320331 :
    adaptiveCoverCheck 9 (childLH (childHH (childHH (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childHH (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childHH (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110320332 :
    adaptiveCoverCheck 9 (childHL (childHH (childHH (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childHH (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childHH (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110320333 :
    adaptiveCoverCheck 9 (childHH (childHH (childHH (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childHH (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childHH (childLL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011032100 :
    adaptiveCoverCheck 10 (childLL (childLL (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011032101 :
    adaptiveCoverCheck 10 (childLH (childLL (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110321020 :
    adaptiveCoverCheck 9 (childLL (childHL (childLL (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childLL (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childLL (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110321021 :
    adaptiveCoverCheck 9 (childLH (childHL (childLL (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childLL (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childLL (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110321022 :
    adaptiveCoverCheck 9 (childHL (childHL (childLL (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childLL (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childLL (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110321023 :
    adaptiveCoverCheck 9 (childHH (childHL (childLL (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childLL (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childLL (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

end PartE
end GerverSofa
