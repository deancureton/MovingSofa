import GerverSofa.KernelOnly.PartE.E24KC2ProofHelpers

/-! E24KC5 checkpoint-aware kernel batch. -/
noncomputable section

namespace GerverSofa
namespace PartE

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00003121 :
    adaptiveCoverCheck 11 (childLH (childHL (childLH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childHL (childLH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHL (childLH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000031220 :
    adaptiveCoverCheck 10 (childLL (childHL (childHL (childLH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHL (childHL (childLH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHL (childHL (childLH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000031221 :
    adaptiveCoverCheck 10 (childLH (childHL (childHL (childLH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHL (childHL (childLH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHL (childHL (childLH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000031222 :
    adaptiveCoverCheck 10 (childHL (childHL (childHL (childLH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHL (childHL (childLH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childHL (childLH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000031223 :
    adaptiveCoverCheck 10 (childHH (childHL (childHL (childLH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHL (childHL (childLH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childHL (childLH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000031230 :
    adaptiveCoverCheck 10 (childLL (childHH (childHL (childLH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHH (childHL (childLH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHH (childHL (childLH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000031231 :
    adaptiveCoverCheck 10 (childLH (childHH (childHL (childLH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHH (childHL (childLH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHH (childHL (childLH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000031232 :
    adaptiveCoverCheck 10 (childHL (childHH (childHL (childLH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHH (childHL (childLH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childHL (childLH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000031233 :
    adaptiveCoverCheck 10 (childHH (childHH (childHL (childLH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHH (childHL (childLH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childHL (childLH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00003130 :
    adaptiveCoverCheck 11 (childLL (childHH (childLH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childHH (childLH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHH (childLH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00003131 :
    adaptiveCoverCheck 11 (childLH (childHH (childLH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childHH (childLH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHH (childLH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000031320 :
    adaptiveCoverCheck 10 (childLL (childHL (childHH (childLH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHL (childHH (childLH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHL (childHH (childLH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000031321 :
    adaptiveCoverCheck 10 (childLH (childHL (childHH (childLH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHL (childHH (childLH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHL (childHH (childLH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000031322 :
    adaptiveCoverCheck 10 (childHL (childHL (childHH (childLH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHL (childHH (childLH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childHH (childLH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000031323 :
    adaptiveCoverCheck 10 (childHH (childHL (childHH (childLH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHL (childHH (childLH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childHH (childLH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000031330 :
    adaptiveCoverCheck 10 (childLL (childHH (childHH (childLH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHH (childHH (childLH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHH (childHH (childLH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000031331 :
    adaptiveCoverCheck 10 (childLH (childHH (childHH (childLH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHH (childHH (childLH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHH (childHH (childLH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000031332 :
    adaptiveCoverCheck 10 (childHL (childHH (childHH (childLH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHH (childHH (childLH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childHH (childLH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000031333 :
    adaptiveCoverCheck 10 (childHH (childHH (childHH (childLH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHH (childHH (childLH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childHH (childLH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000320000 :
    adaptiveCoverCheck 9 (childLL (childLL (childLL (childLL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childLL (childLL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childLL (childLL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000320001 :
    adaptiveCoverCheck 9 (childLH (childLL (childLL (childLL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childLL (childLL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childLL (childLL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000320010 :
    adaptiveCoverCheck 9 (childLL (childLH (childLL (childLL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childLL (childLL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childLL (childLL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000320011 :
    adaptiveCoverCheck 9 (childLH (childLH (childLL (childLL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childLL (childLL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childLL (childLL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000320100 :
    adaptiveCoverCheck 9 (childLL (childLL (childLH (childLL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childLH (childLL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childLH (childLL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000320101 :
    adaptiveCoverCheck 9 (childLH (childLL (childLH (childLL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childLH (childLL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childLH (childLL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000320110 :
    adaptiveCoverCheck 9 (childLL (childLH (childLH (childLL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childLH (childLL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childLH (childLL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000320111 :
    adaptiveCoverCheck 9 (childLH (childLH (childLH (childLL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childLH (childLL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childLH (childLL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000320200 :
    adaptiveCoverCheck 9 (childLL (childLL (childHL (childLL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHL (childLL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHL (childLL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000320201 :
    adaptiveCoverCheck 9 (childLH (childLL (childHL (childLL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHL (childLL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHL (childLL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000320202 :
    adaptiveCoverCheck 9 (childHL (childLL (childHL (childLL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHL (childLL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHL (childLL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000320203 :
    adaptiveCoverCheck 9 (childHH (childLL (childHL (childLL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHL (childLL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHL (childLL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000320210 :
    adaptiveCoverCheck 9 (childLL (childLH (childHL (childLL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childHL (childLL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHL (childLL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000320211 :
    adaptiveCoverCheck 9 (childLH (childLH (childHL (childLL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childHL (childLL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHL (childLL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000320212 :
    adaptiveCoverCheck 9 (childHL (childLH (childHL (childLL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHL (childLL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHL (childLL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000320213 :
    adaptiveCoverCheck 9 (childHH (childLH (childHL (childLL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHL (childLL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHL (childLL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000032022 :
    adaptiveCoverCheck 10 (childHL (childHL (childLL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHL (childLL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childLL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000032023 :
    adaptiveCoverCheck 10 (childHH (childHL (childLL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHL (childLL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childLL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000320300 :
    adaptiveCoverCheck 9 (childLL (childLL (childHH (childLL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHH (childLL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHH (childLL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000320301 :
    adaptiveCoverCheck 9 (childLH (childLL (childHH (childLL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHH (childLL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHH (childLL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000320302 :
    adaptiveCoverCheck 9 (childHL (childLL (childHH (childLL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHH (childLL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHH (childLL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000320303 :
    adaptiveCoverCheck 9 (childHH (childLL (childHH (childLL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHH (childLL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHH (childLL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000320310 :
    adaptiveCoverCheck 9 (childLL (childLH (childHH (childLL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childHH (childLL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHH (childLL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000320311 :
    adaptiveCoverCheck 9 (childLH (childLH (childHH (childLL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childHH (childLL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHH (childLL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000320312 :
    adaptiveCoverCheck 9 (childHL (childLH (childHH (childLL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHH (childLL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHH (childLL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000320313 :
    adaptiveCoverCheck 9 (childHH (childLH (childHH (childLL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHH (childLL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHH (childLL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000032032 :
    adaptiveCoverCheck 10 (childHL (childHH (childLL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHH (childLL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childLL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000032033 :
    adaptiveCoverCheck 10 (childHH (childHH (childLL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHH (childLL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childLL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000321000 :
    adaptiveCoverCheck 9 (childLL (childLL (childLL (childLH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childLL (childLH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childLL (childLH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000321001 :
    adaptiveCoverCheck 9 (childLH (childLL (childLL (childLH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childLL (childLH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childLL (childLH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000321010 :
    adaptiveCoverCheck 9 (childLL (childLH (childLL (childLH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childLL (childLH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childLL (childLH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000321011 :
    adaptiveCoverCheck 9 (childLH (childLH (childLL (childLH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childLL (childLH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childLL (childLH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000321100 :
    adaptiveCoverCheck 9 (childLL (childLL (childLH (childLH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childLH (childLH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childLH (childLH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000321101 :
    adaptiveCoverCheck 9 (childLH (childLL (childLH (childLH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childLH (childLH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childLH (childLH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000321110 :
    adaptiveCoverCheck 9 (childLL (childLH (childLH (childLH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childLH (childLH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childLH (childLH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000321111 :
    adaptiveCoverCheck 9 (childLH (childLH (childLH (childLH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childLH (childLH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childLH (childLH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000321200 :
    adaptiveCoverCheck 9 (childLL (childLL (childHL (childLH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHL (childLH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHL (childLH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000321201 :
    adaptiveCoverCheck 9 (childLH (childLL (childHL (childLH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHL (childLH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHL (childLH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000321202 :
    adaptiveCoverCheck 9 (childHL (childLL (childHL (childLH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHL (childLH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHL (childLH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000321203 :
    adaptiveCoverCheck 9 (childHH (childLL (childHL (childLH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHL (childLH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHL (childLH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000321210 :
    adaptiveCoverCheck 9 (childLL (childLH (childHL (childLH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childHL (childLH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHL (childLH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000321211 :
    adaptiveCoverCheck 9 (childLH (childLH (childHL (childLH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childHL (childLH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHL (childLH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000321212 :
    adaptiveCoverCheck 9 (childHL (childLH (childHL (childLH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHL (childLH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHL (childLH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000321213 :
    adaptiveCoverCheck 9 (childHH (childLH (childHL (childLH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHL (childLH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHL (childLH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000032122 :
    adaptiveCoverCheck 10 (childHL (childHL (childLH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHL (childLH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childLH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000032123 :
    adaptiveCoverCheck 10 (childHH (childHL (childLH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHL (childLH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childLH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000321300 :
    adaptiveCoverCheck 9 (childLL (childLL (childHH (childLH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHH (childLH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHH (childLH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000321301 :
    adaptiveCoverCheck 9 (childLH (childLL (childHH (childLH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHH (childLH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHH (childLH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000321302 :
    adaptiveCoverCheck 9 (childHL (childLL (childHH (childLH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHH (childLH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHH (childLH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000321303 :
    adaptiveCoverCheck 9 (childHH (childLL (childHH (childLH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHH (childLH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHH (childLH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000321310 :
    adaptiveCoverCheck 9 (childLL (childLH (childHH (childLH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childHH (childLH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHH (childLH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000321311 :
    adaptiveCoverCheck 9 (childLH (childLH (childHH (childLH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childHH (childLH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHH (childLH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000321312 :
    adaptiveCoverCheck 9 (childHL (childLH (childHH (childLH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHH (childLH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHH (childLH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000321313 :
    adaptiveCoverCheck 9 (childHH (childLH (childHH (childLH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHH (childLH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHH (childLH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000032132 :
    adaptiveCoverCheck 10 (childHL (childHH (childLH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHH (childLH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childLH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000032133 :
    adaptiveCoverCheck 10 (childHH (childHH (childLH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHH (childLH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childLH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00003220 :
    adaptiveCoverCheck 11 (childLL (childHL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childHL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00003221 :
    adaptiveCoverCheck 11 (childLH (childHL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childHL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00003222 :
    adaptiveCoverCheck 11 (childHL (childHL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00003223 :
    adaptiveCoverCheck 11 (childHH (childHL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00003230 :
    adaptiveCoverCheck 11 (childLL (childHH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childHH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00003231 :
    adaptiveCoverCheck 11 (childLH (childHH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childHH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00003232 :
    adaptiveCoverCheck 11 (childHL (childHH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00003233 :
    adaptiveCoverCheck 11 (childHH (childHH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childHL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000330000 :
    adaptiveCoverCheck 9 (childLL (childLL (childLL (childLL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childLL (childLL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childLL (childLL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000330001 :
    adaptiveCoverCheck 9 (childLH (childLL (childLL (childLL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childLL (childLL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childLL (childLL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000330010 :
    adaptiveCoverCheck 9 (childLL (childLH (childLL (childLL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childLL (childLL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childLL (childLL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000330011 :
    adaptiveCoverCheck 9 (childLH (childLH (childLL (childLL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childLL (childLL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childLL (childLL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000330100 :
    adaptiveCoverCheck 9 (childLL (childLL (childLH (childLL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childLH (childLL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childLH (childLL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000330101 :
    adaptiveCoverCheck 9 (childLH (childLL (childLH (childLL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childLH (childLL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childLH (childLL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000330110 :
    adaptiveCoverCheck 9 (childLL (childLH (childLH (childLL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childLH (childLL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childLH (childLL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000330111 :
    adaptiveCoverCheck 9 (childLH (childLH (childLH (childLL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childLH (childLL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childLH (childLL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000330200 :
    adaptiveCoverCheck 9 (childLL (childLL (childHL (childLL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHL (childLL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHL (childLL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000330201 :
    adaptiveCoverCheck 9 (childLH (childLL (childHL (childLL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHL (childLL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHL (childLL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000330202 :
    adaptiveCoverCheck 9 (childHL (childLL (childHL (childLL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHL (childLL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHL (childLL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000330203 :
    adaptiveCoverCheck 9 (childHH (childLL (childHL (childLL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHL (childLL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHL (childLL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000330210 :
    adaptiveCoverCheck 9 (childLL (childLH (childHL (childLL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childHL (childLL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHL (childLL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000330211 :
    adaptiveCoverCheck 9 (childLH (childLH (childHL (childLL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childHL (childLL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHL (childLL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000330212 :
    adaptiveCoverCheck 9 (childHL (childLH (childHL (childLL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHL (childLL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHL (childLL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000330213 :
    adaptiveCoverCheck 9 (childHH (childLH (childHL (childLL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHL (childLL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHL (childLL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000033022 :
    adaptiveCoverCheck 10 (childHL (childHL (childLL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHL (childLL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childLL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000033023 :
    adaptiveCoverCheck 10 (childHH (childHL (childLL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHL (childLL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childLL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000330300 :
    adaptiveCoverCheck 9 (childLL (childLL (childHH (childLL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHH (childLL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHH (childLL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000330301 :
    adaptiveCoverCheck 9 (childLH (childLL (childHH (childLL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHH (childLL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHH (childLL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000330302 :
    adaptiveCoverCheck 9 (childHL (childLL (childHH (childLL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHH (childLL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHH (childLL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000330303 :
    adaptiveCoverCheck 9 (childHH (childLL (childHH (childLL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHH (childLL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHH (childLL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000330310 :
    adaptiveCoverCheck 9 (childLL (childLH (childHH (childLL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childHH (childLL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHH (childLL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000330311 :
    adaptiveCoverCheck 9 (childLH (childLH (childHH (childLL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childHH (childLL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHH (childLL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000330312 :
    adaptiveCoverCheck 9 (childHL (childLH (childHH (childLL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHH (childLL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHH (childLL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000330313 :
    adaptiveCoverCheck 9 (childHH (childLH (childHH (childLL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHH (childLL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHH (childLL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000033032 :
    adaptiveCoverCheck 10 (childHL (childHH (childLL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHH (childLL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childLL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000033033 :
    adaptiveCoverCheck 10 (childHH (childHH (childLL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHH (childLL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childLL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000331000 :
    adaptiveCoverCheck 9 (childLL (childLL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000331001 :
    adaptiveCoverCheck 9 (childLH (childLL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000331010 :
    adaptiveCoverCheck 9 (childLL (childLH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000331011 :
    adaptiveCoverCheck 9 (childLH (childLH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childLL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000331100 :
    adaptiveCoverCheck 9 (childLL (childLL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000331101 :
    adaptiveCoverCheck 9 (childLH (childLL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000331110 :
    adaptiveCoverCheck 9 (childLL (childLH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000331111 :
    adaptiveCoverCheck 9 (childLH (childLH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childLH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000331200 :
    adaptiveCoverCheck 9 (childLL (childLL (childHL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000331201 :
    adaptiveCoverCheck 9 (childLH (childLL (childHL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000331202 :
    adaptiveCoverCheck 9 (childHL (childLL (childHL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000331203 :
    adaptiveCoverCheck 9 (childHH (childLL (childHL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000331210 :
    adaptiveCoverCheck 9 (childLL (childLH (childHL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childHL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000331211 :
    adaptiveCoverCheck 9 (childLH (childLH (childHL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childHL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000331212 :
    adaptiveCoverCheck 9 (childHL (childLH (childHL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000331213 :
    adaptiveCoverCheck 9 (childHH (childLH (childHL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000033122 :
    adaptiveCoverCheck 10 (childHL (childHL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000033123 :
    adaptiveCoverCheck 10 (childHH (childHL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000331300 :
    adaptiveCoverCheck 9 (childLL (childLL (childHH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000331301 :
    adaptiveCoverCheck 9 (childLH (childLL (childHH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000331302 :
    adaptiveCoverCheck 9 (childHL (childLL (childHH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000331303 :
    adaptiveCoverCheck 9 (childHH (childLL (childHH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000331310 :
    adaptiveCoverCheck 9 (childLL (childLH (childHH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childHH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000331311 :
    adaptiveCoverCheck 9 (childLH (childLH (childHH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childHH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000331312 :
    adaptiveCoverCheck 9 (childHL (childLH (childHH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000331313 :
    adaptiveCoverCheck 9 (childHH (childLH (childHH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000033132 :
    adaptiveCoverCheck 10 (childHL (childHH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000033133 :
    adaptiveCoverCheck 10 (childHH (childHH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childLH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00003320 :
    adaptiveCoverCheck 11 (childLL (childHL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childHL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00003321 :
    adaptiveCoverCheck 11 (childLH (childHL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childHL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00003322 :
    adaptiveCoverCheck 11 (childHL (childHL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00003323 :
    adaptiveCoverCheck 11 (childHH (childHL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00003330 :
    adaptiveCoverCheck 11 (childLL (childHH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childHH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00003331 :
    adaptiveCoverCheck 11 (childLH (childHH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childHH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00003332 :
    adaptiveCoverCheck 11 (childHL (childHH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00003333 :
    adaptiveCoverCheck 11 (childHH (childHH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childHH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000100 :
    adaptiveCoverCheck 13 (childLL (childLL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))) = true := by
  have h : ((childLL (childLL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL (childLL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000101 :
    adaptiveCoverCheck 13 (childLH (childLL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))) = true := by
  have h : ((childLH (childLL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH (childLL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000102 :
    adaptiveCoverCheck 13 (childHL (childLL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))) = true := by
  have h : ((childHL (childLL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000103 :
    adaptiveCoverCheck 13 (childHH (childLL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))) = true := by
  have h : ((childHH (childLL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000110 :
    adaptiveCoverCheck 13 (childLL (childLH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))) = true := by
  have h : ((childLL (childLH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL (childLH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000111 :
    adaptiveCoverCheck 13 (childLH (childLH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))) = true := by
  have h : ((childLH (childLH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH (childLH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000112 :
    adaptiveCoverCheck 13 (childHL (childLH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))) = true := by
  have h : ((childHL (childLH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000113 :
    adaptiveCoverCheck 13 (childHH (childLH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))) = true := by
  have h : ((childHH (childLH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001200 :
    adaptiveCoverCheck 12 (childLL (childLL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childLL (childLL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001201 :
    adaptiveCoverCheck 12 (childLH (childLL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childLH (childLL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00012020 :
    adaptiveCoverCheck 11 (childLL (childHL (childLL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childHL (childLL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHL (childLL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00012021 :
    adaptiveCoverCheck 11 (childLH (childHL (childLL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childHL (childLL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHL (childLL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000120220 :
    adaptiveCoverCheck 10 (childLL (childHL (childHL (childLL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHL (childHL (childLL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHL (childHL (childLL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000120221 :
    adaptiveCoverCheck 10 (childLH (childHL (childHL (childLL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHL (childHL (childLL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHL (childHL (childLL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000120222 :
    adaptiveCoverCheck 10 (childHL (childHL (childHL (childLL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHL (childHL (childLL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childHL (childLL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000120223 :
    adaptiveCoverCheck 10 (childHH (childHL (childHL (childLL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHL (childHL (childLL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childHL (childLL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000120230 :
    adaptiveCoverCheck 10 (childLL (childHH (childHL (childLL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHH (childHL (childLL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHH (childHL (childLL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000120231 :
    adaptiveCoverCheck 10 (childLH (childHH (childHL (childLL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHH (childHL (childLL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHH (childHL (childLL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000120232 :
    adaptiveCoverCheck 10 (childHL (childHH (childHL (childLL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHH (childHL (childLL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childHL (childLL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000120233 :
    adaptiveCoverCheck 10 (childHH (childHH (childHL (childLL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHH (childHL (childLL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childHL (childLL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00012030 :
    adaptiveCoverCheck 11 (childLL (childHH (childLL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childHH (childLL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHH (childLL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00012031 :
    adaptiveCoverCheck 11 (childLH (childHH (childLL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childHH (childLL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHH (childLL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000120320 :
    adaptiveCoverCheck 10 (childLL (childHL (childHH (childLL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHL (childHH (childLL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHL (childHH (childLL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000120321 :
    adaptiveCoverCheck 10 (childLH (childHL (childHH (childLL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHL (childHH (childLL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHL (childHH (childLL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000120322 :
    adaptiveCoverCheck 10 (childHL (childHL (childHH (childLL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHL (childHH (childLL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childHH (childLL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000120323 :
    adaptiveCoverCheck 10 (childHH (childHL (childHH (childLL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHL (childHH (childLL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childHH (childLL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000120330 :
    adaptiveCoverCheck 10 (childLL (childHH (childHH (childLL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHH (childHH (childLL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHH (childHH (childLL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000120331 :
    adaptiveCoverCheck 10 (childLH (childHH (childHH (childLL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHH (childHH (childLL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHH (childHH (childLL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000120332 :
    adaptiveCoverCheck 10 (childHL (childHH (childHH (childLL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHH (childHH (childLL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childHH (childLL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000120333 :
    adaptiveCoverCheck 10 (childHH (childHH (childHH (childLL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHH (childHH (childLL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childHH (childLL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001210 :
    adaptiveCoverCheck 12 (childLL (childLH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childLL (childLH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001211 :
    adaptiveCoverCheck 12 (childLH (childLH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childLH (childLH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00012120 :
    adaptiveCoverCheck 11 (childLL (childHL (childLH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childHL (childLH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHL (childLH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00012121 :
    adaptiveCoverCheck 11 (childLH (childHL (childLH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childHL (childLH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHL (childLH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000121220 :
    adaptiveCoverCheck 10 (childLL (childHL (childHL (childLH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHL (childHL (childLH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHL (childHL (childLH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000121221 :
    adaptiveCoverCheck 10 (childLH (childHL (childHL (childLH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHL (childHL (childLH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHL (childHL (childLH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000121222 :
    adaptiveCoverCheck 10 (childHL (childHL (childHL (childLH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHL (childHL (childLH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childHL (childLH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000121223 :
    adaptiveCoverCheck 10 (childHH (childHL (childHL (childLH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHL (childHL (childLH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childHL (childLH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000121230 :
    adaptiveCoverCheck 10 (childLL (childHH (childHL (childLH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHH (childHL (childLH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHH (childHL (childLH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000121231 :
    adaptiveCoverCheck 10 (childLH (childHH (childHL (childLH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHH (childHL (childLH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHH (childHL (childLH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000121232 :
    adaptiveCoverCheck 10 (childHL (childHH (childHL (childLH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHH (childHL (childLH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childHL (childLH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000121233 :
    adaptiveCoverCheck 10 (childHH (childHH (childHL (childLH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHH (childHL (childLH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childHL (childLH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00012130 :
    adaptiveCoverCheck 11 (childLL (childHH (childLH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childHH (childLH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHH (childLH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00012131 :
    adaptiveCoverCheck 11 (childLH (childHH (childLH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childHH (childLH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHH (childLH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000121320 :
    adaptiveCoverCheck 10 (childLL (childHL (childHH (childLH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHL (childHH (childLH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHL (childHH (childLH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000121321 :
    adaptiveCoverCheck 10 (childLH (childHL (childHH (childLH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHL (childHH (childLH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHL (childHH (childLH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000121322 :
    adaptiveCoverCheck 10 (childHL (childHL (childHH (childLH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHL (childHH (childLH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childHH (childLH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000121323 :
    adaptiveCoverCheck 10 (childHH (childHL (childHH (childLH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHL (childHH (childLH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childHH (childLH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000121330 :
    adaptiveCoverCheck 10 (childLL (childHH (childHH (childLH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHH (childHH (childLH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHH (childHH (childLH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000121331 :
    adaptiveCoverCheck 10 (childLH (childHH (childHH (childLH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHH (childHH (childLH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHH (childHH (childLH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000121332 :
    adaptiveCoverCheck 10 (childHL (childHH (childHH (childLH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHH (childHH (childLH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childHH (childLH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000121333 :
    adaptiveCoverCheck 10 (childHH (childHH (childHH (childLH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHH (childHH (childLH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childHH (childLH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001220000 :
    adaptiveCoverCheck 9 (childLL (childLL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001220001 :
    adaptiveCoverCheck 9 (childLH (childLL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001220010 :
    adaptiveCoverCheck 9 (childLL (childLH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001220011 :
    adaptiveCoverCheck 9 (childLH (childLH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childLL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001220100 :
    adaptiveCoverCheck 9 (childLL (childLL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001220101 :
    adaptiveCoverCheck 9 (childLH (childLL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001220110 :
    adaptiveCoverCheck 9 (childLL (childLH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001220111 :
    adaptiveCoverCheck 9 (childLH (childLH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childLH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001220200 :
    adaptiveCoverCheck 9 (childLL (childLL (childHL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001220201 :
    adaptiveCoverCheck 9 (childLH (childLL (childHL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001220202 :
    adaptiveCoverCheck 9 (childHL (childLL (childHL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001220203 :
    adaptiveCoverCheck 9 (childHH (childLL (childHL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001220210 :
    adaptiveCoverCheck 9 (childLL (childLH (childHL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childHL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001220211 :
    adaptiveCoverCheck 9 (childLH (childLH (childHL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childHL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001220212 :
    adaptiveCoverCheck 9 (childHL (childLH (childHL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001220213 :
    adaptiveCoverCheck 9 (childHH (childLH (childHL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000122022 :
    adaptiveCoverCheck 10 (childHL (childHL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000122023 :
    adaptiveCoverCheck 10 (childHH (childHL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001220300 :
    adaptiveCoverCheck 9 (childLL (childLL (childHH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001220301 :
    adaptiveCoverCheck 9 (childLH (childLL (childHH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001220302 :
    adaptiveCoverCheck 9 (childHL (childLL (childHH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001220303 :
    adaptiveCoverCheck 9 (childHH (childLL (childHH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001220310 :
    adaptiveCoverCheck 9 (childLL (childLH (childHH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childHH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001220311 :
    adaptiveCoverCheck 9 (childLH (childLH (childHH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childHH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001220312 :
    adaptiveCoverCheck 9 (childHL (childLH (childHH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001220313 :
    adaptiveCoverCheck 9 (childHH (childLH (childHH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000122032 :
    adaptiveCoverCheck 10 (childHL (childHH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000122033 :
    adaptiveCoverCheck 10 (childHH (childHH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childLL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001221000 :
    adaptiveCoverCheck 9 (childLL (childLL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001221001 :
    adaptiveCoverCheck 9 (childLH (childLL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001221010 :
    adaptiveCoverCheck 9 (childLL (childLH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001221011 :
    adaptiveCoverCheck 9 (childLH (childLH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childLL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001221100 :
    adaptiveCoverCheck 9 (childLL (childLL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001221101 :
    adaptiveCoverCheck 9 (childLH (childLL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001221110 :
    adaptiveCoverCheck 9 (childLL (childLH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001221111 :
    adaptiveCoverCheck 9 (childLH (childLH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childLH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001221200 :
    adaptiveCoverCheck 9 (childLL (childLL (childHL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001221201 :
    adaptiveCoverCheck 9 (childLH (childLL (childHL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001221202 :
    adaptiveCoverCheck 9 (childHL (childLL (childHL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001221203 :
    adaptiveCoverCheck 9 (childHH (childLL (childHL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001221210 :
    adaptiveCoverCheck 9 (childLL (childLH (childHL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childHL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001221211 :
    adaptiveCoverCheck 9 (childLH (childLH (childHL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childHL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001221212 :
    adaptiveCoverCheck 9 (childHL (childLH (childHL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001221213 :
    adaptiveCoverCheck 9 (childHH (childLH (childHL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000122122 :
    adaptiveCoverCheck 10 (childHL (childHL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000122123 :
    adaptiveCoverCheck 10 (childHH (childHL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001221300 :
    adaptiveCoverCheck 9 (childLL (childLL (childHH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001221301 :
    adaptiveCoverCheck 9 (childLH (childLL (childHH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001221302 :
    adaptiveCoverCheck 9 (childHL (childLL (childHH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001221303 :
    adaptiveCoverCheck 9 (childHH (childLL (childHH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001221310 :
    adaptiveCoverCheck 9 (childLL (childLH (childHH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childHH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001221311 :
    adaptiveCoverCheck 9 (childLH (childLH (childHH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childHH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001221312 :
    adaptiveCoverCheck 9 (childHL (childLH (childHH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001221313 :
    adaptiveCoverCheck 9 (childHH (childLH (childHH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000122132 :
    adaptiveCoverCheck 10 (childHL (childHH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000122133 :
    adaptiveCoverCheck 10 (childHH (childHH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childLH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00012220 :
    adaptiveCoverCheck 11 (childLL (childHL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childHL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00012221 :
    adaptiveCoverCheck 11 (childLH (childHL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childHL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00012222 :
    adaptiveCoverCheck 11 (childHL (childHL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00012223 :
    adaptiveCoverCheck 11 (childHH (childHL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00012230 :
    adaptiveCoverCheck 11 (childLL (childHH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childHH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00012231 :
    adaptiveCoverCheck 11 (childLH (childHH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childHH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00012232 :
    adaptiveCoverCheck 11 (childHL (childHH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00012233 :
    adaptiveCoverCheck 11 (childHH (childHH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childHL (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001230000 :
    adaptiveCoverCheck 9 (childLL (childLL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001230001 :
    adaptiveCoverCheck 9 (childLH (childLL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001230010 :
    adaptiveCoverCheck 9 (childLL (childLH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001230011 :
    adaptiveCoverCheck 9 (childLH (childLH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childLL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001230100 :
    adaptiveCoverCheck 9 (childLL (childLL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001230101 :
    adaptiveCoverCheck 9 (childLH (childLL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001230110 :
    adaptiveCoverCheck 9 (childLL (childLH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001230111 :
    adaptiveCoverCheck 9 (childLH (childLH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childLH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001230200 :
    adaptiveCoverCheck 9 (childLL (childLL (childHL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001230201 :
    adaptiveCoverCheck 9 (childLH (childLL (childHL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001230202 :
    adaptiveCoverCheck 9 (childHL (childLL (childHL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001230203 :
    adaptiveCoverCheck 9 (childHH (childLL (childHL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001230210 :
    adaptiveCoverCheck 9 (childLL (childLH (childHL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childHL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001230211 :
    adaptiveCoverCheck 9 (childLH (childLH (childHL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childHL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001230212 :
    adaptiveCoverCheck 9 (childHL (childLH (childHL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001230213 :
    adaptiveCoverCheck 9 (childHH (childLH (childHL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000123022 :
    adaptiveCoverCheck 10 (childHL (childHL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000123023 :
    adaptiveCoverCheck 10 (childHH (childHL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001230300 :
    adaptiveCoverCheck 9 (childLL (childLL (childHH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001230301 :
    adaptiveCoverCheck 9 (childLH (childLL (childHH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001230302 :
    adaptiveCoverCheck 9 (childHL (childLL (childHH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001230303 :
    adaptiveCoverCheck 9 (childHH (childLL (childHH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001230310 :
    adaptiveCoverCheck 9 (childLL (childLH (childHH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childHH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001230311 :
    adaptiveCoverCheck 9 (childLH (childLH (childHH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childHH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001230312 :
    adaptiveCoverCheck 9 (childHL (childLH (childHH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001230313 :
    adaptiveCoverCheck 9 (childHH (childLH (childHH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000123032 :
    adaptiveCoverCheck 10 (childHL (childHH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000123033 :
    adaptiveCoverCheck 10 (childHH (childHH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childLL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001231000 :
    adaptiveCoverCheck 9 (childLL (childLL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001231001 :
    adaptiveCoverCheck 9 (childLH (childLL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001231003 :
    adaptiveCoverCheck 9 (childHH (childLL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001231010 :
    adaptiveCoverCheck 9 (childLL (childLH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001231011 :
    adaptiveCoverCheck 9 (childLH (childLH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001231012 :
    adaptiveCoverCheck 9 (childHL (childLH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001231013 :
    adaptiveCoverCheck 9 (childHH (childLH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childLL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001231100 :
    adaptiveCoverCheck 9 (childLL (childLL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001231101 :
    adaptiveCoverCheck 9 (childLH (childLL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001231102 :
    adaptiveCoverCheck 9 (childHL (childLL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001231103 :
    adaptiveCoverCheck 9 (childHH (childLL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001231110 :
    adaptiveCoverCheck 9 (childLL (childLH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001231111 :
    adaptiveCoverCheck 9 (childLH (childLH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001231112 :
    adaptiveCoverCheck 9 (childHL (childLH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001231113 :
    adaptiveCoverCheck 9 (childHH (childLH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childLH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001231200 :
    adaptiveCoverCheck 9 (childLL (childLL (childHL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001231201 :
    adaptiveCoverCheck 9 (childLH (childLL (childHL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001231202 :
    adaptiveCoverCheck 9 (childHL (childLL (childHL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001231203 :
    adaptiveCoverCheck 9 (childHH (childLL (childHL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001231210 :
    adaptiveCoverCheck 9 (childLL (childLH (childHL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childHL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001231211 :
    adaptiveCoverCheck 9 (childLH (childLH (childHL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childHL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001231212 :
    adaptiveCoverCheck 9 (childHL (childLH (childHL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001231213 :
    adaptiveCoverCheck 9 (childHH (childLH (childHL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000123122 :
    adaptiveCoverCheck 10 (childHL (childHL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000123123 :
    adaptiveCoverCheck 10 (childHH (childHL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001231300 :
    adaptiveCoverCheck 9 (childLL (childLL (childHH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001231301 :
    adaptiveCoverCheck 9 (childLH (childLL (childHH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001231302 :
    adaptiveCoverCheck 9 (childHL (childLL (childHH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001231303 :
    adaptiveCoverCheck 9 (childHH (childLL (childHH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001231310 :
    adaptiveCoverCheck 9 (childLL (childLH (childHH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childHH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001231311 :
    adaptiveCoverCheck 9 (childLH (childLH (childHH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childHH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001231312 :
    adaptiveCoverCheck 9 (childHL (childLH (childHH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001231313 :
    adaptiveCoverCheck 9 (childHH (childLH (childHH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000123132 :
    adaptiveCoverCheck 10 (childHL (childHH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000123133 :
    adaptiveCoverCheck 10 (childHH (childHH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childLH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00012320 :
    adaptiveCoverCheck 11 (childLL (childHL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childHL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00012321 :
    adaptiveCoverCheck 11 (childLH (childHL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childHL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00012322 :
    adaptiveCoverCheck 11 (childHL (childHL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00012323 :
    adaptiveCoverCheck 11 (childHH (childHL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00012330 :
    adaptiveCoverCheck 11 (childLL (childHH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childHH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00012331 :
    adaptiveCoverCheck 11 (childLH (childHH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childHH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00012332 :
    adaptiveCoverCheck 11 (childHL (childHH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00012333 :
    adaptiveCoverCheck 11 (childHH (childHH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childHH (childHL (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001300 :
    adaptiveCoverCheck 12 (childLL (childLL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childLL (childLL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001301 :
    adaptiveCoverCheck 12 (childLH (childLL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childLH (childLL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00013020 :
    adaptiveCoverCheck 11 (childLL (childHL (childLL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childHL (childLL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHL (childLL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00013021 :
    adaptiveCoverCheck 11 (childLH (childHL (childLL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childHL (childLL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHL (childLL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000130220 :
    adaptiveCoverCheck 10 (childLL (childHL (childHL (childLL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHL (childHL (childLL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHL (childHL (childLL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000130221 :
    adaptiveCoverCheck 10 (childLH (childHL (childHL (childLL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHL (childHL (childLL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHL (childHL (childLL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000130222 :
    adaptiveCoverCheck 10 (childHL (childHL (childHL (childLL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHL (childHL (childLL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childHL (childLL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000130223 :
    adaptiveCoverCheck 10 (childHH (childHL (childHL (childLL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHL (childHL (childLL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childHL (childLL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000130230 :
    adaptiveCoverCheck 10 (childLL (childHH (childHL (childLL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHH (childHL (childLL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHH (childHL (childLL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000130231 :
    adaptiveCoverCheck 10 (childLH (childHH (childHL (childLL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHH (childHL (childLL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHH (childHL (childLL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000130232 :
    adaptiveCoverCheck 10 (childHL (childHH (childHL (childLL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHH (childHL (childLL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childHL (childLL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000130233 :
    adaptiveCoverCheck 10 (childHH (childHH (childHL (childLL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHH (childHL (childLL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childHL (childLL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00013030 :
    adaptiveCoverCheck 11 (childLL (childHH (childLL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childHH (childLL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHH (childLL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00013031 :
    adaptiveCoverCheck 11 (childLH (childHH (childLL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childHH (childLL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHH (childLL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000130320 :
    adaptiveCoverCheck 10 (childLL (childHL (childHH (childLL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHL (childHH (childLL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHL (childHH (childLL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000130321 :
    adaptiveCoverCheck 10 (childLH (childHL (childHH (childLL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHL (childHH (childLL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHL (childHH (childLL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000130322 :
    adaptiveCoverCheck 10 (childHL (childHL (childHH (childLL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHL (childHH (childLL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childHH (childLL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000130323 :
    adaptiveCoverCheck 10 (childHH (childHL (childHH (childLL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHL (childHH (childLL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childHH (childLL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000130330 :
    adaptiveCoverCheck 10 (childLL (childHH (childHH (childLL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHH (childHH (childLL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHH (childHH (childLL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000130331 :
    adaptiveCoverCheck 10 (childLH (childHH (childHH (childLL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHH (childHH (childLL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHH (childHH (childLL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000130332 :
    adaptiveCoverCheck 10 (childHL (childHH (childHH (childLL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHH (childHH (childLL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childHH (childLL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000130333 :
    adaptiveCoverCheck 10 (childHH (childHH (childHH (childLL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHH (childHH (childLL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childHH (childLL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001310 :
    adaptiveCoverCheck 12 (childLL (childLH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childLL (childLH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001311 :
    adaptiveCoverCheck 12 (childLH (childLH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childLH (childLH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00013120 :
    adaptiveCoverCheck 11 (childLL (childHL (childLH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childHL (childLH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHL (childLH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00013121 :
    adaptiveCoverCheck 11 (childLH (childHL (childLH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childHL (childLH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHL (childLH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000131220 :
    adaptiveCoverCheck 10 (childLL (childHL (childHL (childLH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHL (childHL (childLH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHL (childHL (childLH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000131221 :
    adaptiveCoverCheck 10 (childLH (childHL (childHL (childLH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHL (childHL (childLH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHL (childHL (childLH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000131222 :
    adaptiveCoverCheck 10 (childHL (childHL (childHL (childLH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHL (childHL (childLH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childHL (childLH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000131223 :
    adaptiveCoverCheck 10 (childHH (childHL (childHL (childLH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHL (childHL (childLH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childHL (childLH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000131230 :
    adaptiveCoverCheck 10 (childLL (childHH (childHL (childLH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHH (childHL (childLH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHH (childHL (childLH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000131231 :
    adaptiveCoverCheck 10 (childLH (childHH (childHL (childLH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHH (childHL (childLH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHH (childHL (childLH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000131232 :
    adaptiveCoverCheck 10 (childHL (childHH (childHL (childLH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHH (childHL (childLH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childHL (childLH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000131233 :
    adaptiveCoverCheck 10 (childHH (childHH (childHL (childLH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHH (childHL (childLH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childHL (childLH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00013130 :
    adaptiveCoverCheck 11 (childLL (childHH (childLH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childHH (childLH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHH (childLH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00013131 :
    adaptiveCoverCheck 11 (childLH (childHH (childLH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childHH (childLH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHH (childLH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000131320 :
    adaptiveCoverCheck 10 (childLL (childHL (childHH (childLH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHL (childHH (childLH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHL (childHH (childLH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000131321 :
    adaptiveCoverCheck 10 (childLH (childHL (childHH (childLH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHL (childHH (childLH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHL (childHH (childLH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000131322 :
    adaptiveCoverCheck 10 (childHL (childHL (childHH (childLH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHL (childHH (childLH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childHH (childLH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000131323 :
    adaptiveCoverCheck 10 (childHH (childHL (childHH (childLH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHL (childHH (childLH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childHH (childLH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000131330 :
    adaptiveCoverCheck 10 (childLL (childHH (childHH (childLH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHH (childHH (childLH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHH (childHH (childLH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000131331 :
    adaptiveCoverCheck 10 (childLH (childHH (childHH (childLH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHH (childHH (childLH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHH (childHH (childLH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000131332 :
    adaptiveCoverCheck 10 (childHL (childHH (childHH (childLH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHH (childHH (childLH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childHH (childLH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000131333 :
    adaptiveCoverCheck 10 (childHH (childHH (childHH (childLH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHH (childHH (childLH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childHH (childLH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001320000 :
    adaptiveCoverCheck 9 (childLL (childLL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001320001 :
    adaptiveCoverCheck 9 (childLH (childLL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001320002 :
    adaptiveCoverCheck 9 (childHL (childLL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001320003 :
    adaptiveCoverCheck 9 (childHH (childLL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001320010 :
    adaptiveCoverCheck 9 (childLL (childLH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001320011 :
    adaptiveCoverCheck 9 (childLH (childLH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001320012 :
    adaptiveCoverCheck 9 (childHL (childLH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001320013 :
    adaptiveCoverCheck 9 (childHH (childLH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childLL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001320100 :
    adaptiveCoverCheck 9 (childLL (childLL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001320101 :
    adaptiveCoverCheck 9 (childLH (childLL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001320102 :
    adaptiveCoverCheck 9 (childHL (childLL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001320103 :
    adaptiveCoverCheck 9 (childHH (childLL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001320110 :
    adaptiveCoverCheck 9 (childLL (childLH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001320111 :
    adaptiveCoverCheck 9 (childLH (childLH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001320112 :
    adaptiveCoverCheck 9 (childHL (childLH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001320113 :
    adaptiveCoverCheck 9 (childHH (childLH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childLH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001320200 :
    adaptiveCoverCheck 9 (childLL (childLL (childHL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001320201 :
    adaptiveCoverCheck 9 (childLH (childLL (childHL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001320202 :
    adaptiveCoverCheck 9 (childHL (childLL (childHL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001320203 :
    adaptiveCoverCheck 9 (childHH (childLL (childHL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001320210 :
    adaptiveCoverCheck 9 (childLL (childLH (childHL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childHL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001320211 :
    adaptiveCoverCheck 9 (childLH (childLH (childHL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childHL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001320212 :
    adaptiveCoverCheck 9 (childHL (childLH (childHL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001320213 :
    adaptiveCoverCheck 9 (childHH (childLH (childHL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000132022 :
    adaptiveCoverCheck 10 (childHL (childHL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000132023 :
    adaptiveCoverCheck 10 (childHH (childHL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001320300 :
    adaptiveCoverCheck 9 (childLL (childLL (childHH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001320301 :
    adaptiveCoverCheck 9 (childLH (childLL (childHH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001320302 :
    adaptiveCoverCheck 9 (childHL (childLL (childHH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001320303 :
    adaptiveCoverCheck 9 (childHH (childLL (childHH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001320310 :
    adaptiveCoverCheck 9 (childLL (childLH (childHH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childHH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001320311 :
    adaptiveCoverCheck 9 (childLH (childLH (childHH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childHH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001320312 :
    adaptiveCoverCheck 9 (childHL (childLH (childHH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001320313 :
    adaptiveCoverCheck 9 (childHH (childLH (childHH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000132032 :
    adaptiveCoverCheck 10 (childHL (childHH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000132033 :
    adaptiveCoverCheck 10 (childHH (childHH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childLL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001321000 :
    adaptiveCoverCheck 9 (childLL (childLL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001321001 :
    adaptiveCoverCheck 9 (childLH (childLL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001321002 :
    adaptiveCoverCheck 9 (childHL (childLL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001321003 :
    adaptiveCoverCheck 9 (childHH (childLL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001321010 :
    adaptiveCoverCheck 9 (childLL (childLH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001321011 :
    adaptiveCoverCheck 9 (childLH (childLH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001321012 :
    adaptiveCoverCheck 9 (childHL (childLH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001321013 :
    adaptiveCoverCheck 9 (childHH (childLH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childLL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001321100 :
    adaptiveCoverCheck 9 (childLL (childLL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001321101 :
    adaptiveCoverCheck 9 (childLH (childLL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001321102 :
    adaptiveCoverCheck 9 (childHL (childLL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001321103 :
    adaptiveCoverCheck 9 (childHH (childLL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001321110 :
    adaptiveCoverCheck 9 (childLL (childLH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001321111 :
    adaptiveCoverCheck 9 (childLH (childLH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001321112 :
    adaptiveCoverCheck 9 (childHL (childLH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001321113 :
    adaptiveCoverCheck 9 (childHH (childLH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childLH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001321200 :
    adaptiveCoverCheck 9 (childLL (childLL (childHL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001321201 :
    adaptiveCoverCheck 9 (childLH (childLL (childHL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001321202 :
    adaptiveCoverCheck 9 (childHL (childLL (childHL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001321203 :
    adaptiveCoverCheck 9 (childHH (childLL (childHL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001321210 :
    adaptiveCoverCheck 9 (childLL (childLH (childHL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childHL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001321211 :
    adaptiveCoverCheck 9 (childLH (childLH (childHL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childHL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001321212 :
    adaptiveCoverCheck 9 (childHL (childLH (childHL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001321213 :
    adaptiveCoverCheck 9 (childHH (childLH (childHL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000132122 :
    adaptiveCoverCheck 10 (childHL (childHL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000132123 :
    adaptiveCoverCheck 10 (childHH (childHL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001321300 :
    adaptiveCoverCheck 9 (childLL (childLL (childHH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001321301 :
    adaptiveCoverCheck 9 (childLH (childLL (childHH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001321302 :
    adaptiveCoverCheck 9 (childHL (childLL (childHH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001321303 :
    adaptiveCoverCheck 9 (childHH (childLL (childHH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001321310 :
    adaptiveCoverCheck 9 (childLL (childLH (childHH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childHH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001321311 :
    adaptiveCoverCheck 9 (childLH (childLH (childHH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childHH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001321312 :
    adaptiveCoverCheck 9 (childHL (childLH (childHH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001321313 :
    adaptiveCoverCheck 9 (childHH (childLH (childHH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000132132 :
    adaptiveCoverCheck 10 (childHL (childHH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000132133 :
    adaptiveCoverCheck 10 (childHH (childHH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childLH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00013220 :
    adaptiveCoverCheck 11 (childLL (childHL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childHL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00013221 :
    adaptiveCoverCheck 11 (childLH (childHL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childHL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00013222 :
    adaptiveCoverCheck 11 (childHL (childHL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00013223 :
    adaptiveCoverCheck 11 (childHH (childHL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00013230 :
    adaptiveCoverCheck 11 (childLL (childHH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childHH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00013231 :
    adaptiveCoverCheck 11 (childLH (childHH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childHH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00013232 :
    adaptiveCoverCheck 11 (childHL (childHH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00013233 :
    adaptiveCoverCheck 11 (childHH (childHH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childHL (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001330000 :
    adaptiveCoverCheck 9 (childLL (childLL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001330001 :
    adaptiveCoverCheck 9 (childLH (childLL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001330002 :
    adaptiveCoverCheck 9 (childHL (childLL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001330003 :
    adaptiveCoverCheck 9 (childHH (childLL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001330010 :
    adaptiveCoverCheck 9 (childLL (childLH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001330011 :
    adaptiveCoverCheck 9 (childLH (childLH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001330012 :
    adaptiveCoverCheck 9 (childHL (childLH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001330013 :
    adaptiveCoverCheck 9 (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childLL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001330100 :
    adaptiveCoverCheck 9 (childLL (childLL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001330101 :
    adaptiveCoverCheck 9 (childLH (childLL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001330102 :
    adaptiveCoverCheck 9 (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001330103 :
    adaptiveCoverCheck 9 (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001330110 :
    adaptiveCoverCheck 9 (childLL (childLH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001330111 :
    adaptiveCoverCheck 9 (childLH (childLH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001330112 :
    adaptiveCoverCheck 9 (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001330113 :
    adaptiveCoverCheck 9 (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childLH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001330200 :
    adaptiveCoverCheck 9 (childLL (childLL (childHL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001330201 :
    adaptiveCoverCheck 9 (childLH (childLL (childHL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001330202 :
    adaptiveCoverCheck 9 (childHL (childLL (childHL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001330203 :
    adaptiveCoverCheck 9 (childHH (childLL (childHL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001330210 :
    adaptiveCoverCheck 9 (childLL (childLH (childHL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childHL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001330211 :
    adaptiveCoverCheck 9 (childLH (childLH (childHL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childHL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001330212 :
    adaptiveCoverCheck 9 (childHL (childLH (childHL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001330213 :
    adaptiveCoverCheck 9 (childHH (childLH (childHL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000133022 :
    adaptiveCoverCheck 10 (childHL (childHL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000133023 :
    adaptiveCoverCheck 10 (childHH (childHL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001330300 :
    adaptiveCoverCheck 9 (childLL (childLL (childHH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001330301 :
    adaptiveCoverCheck 9 (childLH (childLL (childHH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001330302 :
    adaptiveCoverCheck 9 (childHL (childLL (childHH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001330303 :
    adaptiveCoverCheck 9 (childHH (childLL (childHH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001330310 :
    adaptiveCoverCheck 9 (childLL (childLH (childHH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childHH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001330311 :
    adaptiveCoverCheck 9 (childLH (childLH (childHH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childHH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001330312 :
    adaptiveCoverCheck 9 (childHL (childLH (childHH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001330313 :
    adaptiveCoverCheck 9 (childHH (childLH (childHH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000133032 :
    adaptiveCoverCheck 10 (childHL (childHH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000133033 :
    adaptiveCoverCheck 10 (childHH (childHH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childLL (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001331000 :
    adaptiveCoverCheck 9 (childLL (childLL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001331001 :
    adaptiveCoverCheck 9 (childLH (childLL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001331002 :
    adaptiveCoverCheck 9 (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001331003 :
    adaptiveCoverCheck 9 (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001331010 :
    adaptiveCoverCheck 9 (childLL (childLH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001331011 :
    adaptiveCoverCheck 9 (childLH (childLH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001331012 :
    adaptiveCoverCheck 9 (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001331013 :
    adaptiveCoverCheck 9 (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childLL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001331100 :
    adaptiveCoverCheck 9 (childLL (childLL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001331101 :
    adaptiveCoverCheck 9 (childLH (childLL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001331102 :
    adaptiveCoverCheck 9 (childHL (childLL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001331103 :
    adaptiveCoverCheck 9 (childHH (childLL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001331110 :
    adaptiveCoverCheck 9 (childLL (childLH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001331111 :
    adaptiveCoverCheck 9 (childLH (childLH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001331112 :
    adaptiveCoverCheck 9 (childHL (childLH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001331113 :
    adaptiveCoverCheck 9 (childHH (childLH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childLH (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001331200 :
    adaptiveCoverCheck 9 (childLL (childLL (childHL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0001331201 :
    adaptiveCoverCheck 9 (childLH (childLL (childHL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHL (childLH (childHH (childHH (childLH (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

end PartE
end GerverSofa
