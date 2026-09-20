import GerverSofa.KernelOnly.PartE.E24KC2ProofHelpers

/-! E24KC5 checkpoint-aware kernel batch. -/
noncomputable section

namespace GerverSofa
namespace PartE

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111123311 :
    adaptiveCoverCheck 10 (childLH (childLH (childHH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childHH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childHH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111123312 :
    adaptiveCoverCheck 10 (childHL (childLH (childHH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLH (childHH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childHH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111123313 :
    adaptiveCoverCheck 10 (childHH (childLH (childHH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLH (childHH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childHH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111123320 :
    adaptiveCoverCheck 10 (childLL (childHL (childHH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHL (childHH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHL (childHH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111123321 :
    adaptiveCoverCheck 10 (childLH (childHL (childHH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHL (childHH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHL (childHH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111123322 :
    adaptiveCoverCheck 10 (childHL (childHL (childHH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHL (childHH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childHH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111123323 :
    adaptiveCoverCheck 10 (childHH (childHL (childHH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHL (childHH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childHH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111123330 :
    adaptiveCoverCheck 10 (childLL (childHH (childHH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHH (childHH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHH (childHH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111123331 :
    adaptiveCoverCheck 10 (childLH (childHH (childHH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHH (childHH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHH (childHH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111123332 :
    adaptiveCoverCheck 10 (childHL (childHH (childHH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHH (childHH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childHH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111123333 :
    adaptiveCoverCheck 10 (childHH (childHH (childHH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHH (childHH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childHH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1111300 :
    adaptiveCoverCheck 12 (childLL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1111301 :
    adaptiveCoverCheck 12 (childLH (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLH (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1111302 :
    adaptiveCoverCheck 12 (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1111303 :
    adaptiveCoverCheck 12 (childHH (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childHH (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1111310 :
    adaptiveCoverCheck 12 (childLL (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLL (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1111311 :
    adaptiveCoverCheck 12 (childLH (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLH (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1111312 :
    adaptiveCoverCheck 12 (childHL (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childHL (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1111313 :
    adaptiveCoverCheck 12 (childHH (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childHH (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11113200 :
    adaptiveCoverCheck 11 (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11113201 :
    adaptiveCoverCheck 11 (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111132020 :
    adaptiveCoverCheck 10 (childLL (childHL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111132021 :
    adaptiveCoverCheck 10 (childLH (childHL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111132022 :
    adaptiveCoverCheck 10 (childHL (childHL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111132023 :
    adaptiveCoverCheck 10 (childHH (childHL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111132030 :
    adaptiveCoverCheck 10 (childLL (childHH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111132031 :
    adaptiveCoverCheck 10 (childLH (childHH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111132032 :
    adaptiveCoverCheck 10 (childHL (childHH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111132033 :
    adaptiveCoverCheck 10 (childHH (childHH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11113210 :
    adaptiveCoverCheck 11 (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11113211 :
    adaptiveCoverCheck 11 (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111132120 :
    adaptiveCoverCheck 10 (childLL (childHL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111132121 :
    adaptiveCoverCheck 10 (childLH (childHL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111132122 :
    adaptiveCoverCheck 10 (childHL (childHL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111132123 :
    adaptiveCoverCheck 10 (childHH (childHL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111132130 :
    adaptiveCoverCheck 10 (childLL (childHH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111132131 :
    adaptiveCoverCheck 10 (childLH (childHH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111132132 :
    adaptiveCoverCheck 10 (childHL (childHH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111132133 :
    adaptiveCoverCheck 10 (childHH (childHH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111132200 :
    adaptiveCoverCheck 10 (childLL (childLL (childHL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childHL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childHL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111132201 :
    adaptiveCoverCheck 10 (childLH (childLL (childHL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childHL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childHL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111132202 :
    adaptiveCoverCheck 10 (childHL (childLL (childHL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLL (childHL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childHL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111132203 :
    adaptiveCoverCheck 10 (childHH (childLL (childHL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLL (childHL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childHL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111132210 :
    adaptiveCoverCheck 10 (childLL (childLH (childHL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childHL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childHL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111132211 :
    adaptiveCoverCheck 10 (childLH (childLH (childHL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childHL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childHL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111132212 :
    adaptiveCoverCheck 10 (childHL (childLH (childHL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLH (childHL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childHL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111132213 :
    adaptiveCoverCheck 10 (childHH (childLH (childHL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLH (childHL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childHL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111132220 :
    adaptiveCoverCheck 10 (childLL (childHL (childHL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHL (childHL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHL (childHL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111132221 :
    adaptiveCoverCheck 10 (childLH (childHL (childHL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHL (childHL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHL (childHL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111132222 :
    adaptiveCoverCheck 10 (childHL (childHL (childHL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHL (childHL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childHL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111132223 :
    adaptiveCoverCheck 10 (childHH (childHL (childHL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHL (childHL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childHL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111132230 :
    adaptiveCoverCheck 10 (childLL (childHH (childHL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHH (childHL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHH (childHL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111132231 :
    adaptiveCoverCheck 10 (childLH (childHH (childHL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHH (childHL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHH (childHL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111132232 :
    adaptiveCoverCheck 10 (childHL (childHH (childHL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHH (childHL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childHL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111132233 :
    adaptiveCoverCheck 10 (childHH (childHH (childHL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHH (childHL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childHL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111132300 :
    adaptiveCoverCheck 10 (childLL (childLL (childHH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childHH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childHH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111132301 :
    adaptiveCoverCheck 10 (childLH (childLL (childHH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childHH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childHH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111132302 :
    adaptiveCoverCheck 10 (childHL (childLL (childHH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLL (childHH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childHH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111132303 :
    adaptiveCoverCheck 10 (childHH (childLL (childHH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLL (childHH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childHH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111132310 :
    adaptiveCoverCheck 10 (childLL (childLH (childHH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childHH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childHH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111132311 :
    adaptiveCoverCheck 10 (childLH (childLH (childHH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childHH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childHH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111132312 :
    adaptiveCoverCheck 10 (childHL (childLH (childHH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLH (childHH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childHH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111132313 :
    adaptiveCoverCheck 10 (childHH (childLH (childHH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLH (childHH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childHH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111132320 :
    adaptiveCoverCheck 10 (childLL (childHL (childHH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHL (childHH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHL (childHH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111132321 :
    adaptiveCoverCheck 10 (childLH (childHL (childHH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHL (childHH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHL (childHH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111132322 :
    adaptiveCoverCheck 10 (childHL (childHL (childHH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHL (childHH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childHH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111132323 :
    adaptiveCoverCheck 10 (childHH (childHL (childHH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHL (childHH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childHH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111132330 :
    adaptiveCoverCheck 10 (childLL (childHH (childHH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHH (childHH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHH (childHH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111132331 :
    adaptiveCoverCheck 10 (childLH (childHH (childHH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHH (childHH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHH (childHH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111132332 :
    adaptiveCoverCheck 10 (childHL (childHH (childHH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHH (childHH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childHH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111132333 :
    adaptiveCoverCheck 10 (childHH (childHH (childHH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHH (childHH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childHH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11113300 :
    adaptiveCoverCheck 11 (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11113301 :
    adaptiveCoverCheck 11 (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111133020 :
    adaptiveCoverCheck 10 (childLL (childHL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111133021 :
    adaptiveCoverCheck 10 (childLH (childHL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111133022 :
    adaptiveCoverCheck 10 (childHL (childHL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111133023 :
    adaptiveCoverCheck 10 (childHH (childHL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111133030 :
    adaptiveCoverCheck 10 (childLL (childHH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111133031 :
    adaptiveCoverCheck 10 (childLH (childHH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111133032 :
    adaptiveCoverCheck 10 (childHL (childHH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111133033 :
    adaptiveCoverCheck 10 (childHH (childHH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11113310 :
    adaptiveCoverCheck 11 (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11113311 :
    adaptiveCoverCheck 11 (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111133120 :
    adaptiveCoverCheck 10 (childLL (childHL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111133121 :
    adaptiveCoverCheck 10 (childLH (childHL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111133122 :
    adaptiveCoverCheck 10 (childHL (childHL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111133123 :
    adaptiveCoverCheck 10 (childHH (childHL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111133130 :
    adaptiveCoverCheck 10 (childLL (childHH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111133131 :
    adaptiveCoverCheck 10 (childLH (childHH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111133132 :
    adaptiveCoverCheck 10 (childHL (childHH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111133133 :
    adaptiveCoverCheck 10 (childHH (childHH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111133200 :
    adaptiveCoverCheck 10 (childLL (childLL (childHL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childHL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childHL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111133201 :
    adaptiveCoverCheck 10 (childLH (childLL (childHL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childHL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childHL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111133202 :
    adaptiveCoverCheck 10 (childHL (childLL (childHL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLL (childHL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childHL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111133203 :
    adaptiveCoverCheck 10 (childHH (childLL (childHL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLL (childHL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childHL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111133210 :
    adaptiveCoverCheck 10 (childLL (childLH (childHL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childHL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childHL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111133211 :
    adaptiveCoverCheck 10 (childLH (childLH (childHL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childHL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childHL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111133212 :
    adaptiveCoverCheck 10 (childHL (childLH (childHL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLH (childHL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childHL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111133213 :
    adaptiveCoverCheck 10 (childHH (childLH (childHL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLH (childHL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childHL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111133220 :
    adaptiveCoverCheck 10 (childLL (childHL (childHL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHL (childHL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHL (childHL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111133221 :
    adaptiveCoverCheck 10 (childLH (childHL (childHL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHL (childHL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHL (childHL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111133222 :
    adaptiveCoverCheck 10 (childHL (childHL (childHL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHL (childHL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childHL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111133223 :
    adaptiveCoverCheck 10 (childHH (childHL (childHL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHL (childHL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childHL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111133230 :
    adaptiveCoverCheck 10 (childLL (childHH (childHL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHH (childHL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHH (childHL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111133231 :
    adaptiveCoverCheck 10 (childLH (childHH (childHL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHH (childHL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHH (childHL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111133232 :
    adaptiveCoverCheck 10 (childHL (childHH (childHL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHH (childHL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childHL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111133233 :
    adaptiveCoverCheck 10 (childHH (childHH (childHL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHH (childHL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childHL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111133300 :
    adaptiveCoverCheck 10 (childLL (childLL (childHH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childHH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childHH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111133301 :
    adaptiveCoverCheck 10 (childLH (childLL (childHH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childHH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childHH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111133302 :
    adaptiveCoverCheck 10 (childHL (childLL (childHH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLL (childHH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childHH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111133303 :
    adaptiveCoverCheck 10 (childHH (childLL (childHH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLL (childHH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childHH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111133310 :
    adaptiveCoverCheck 10 (childLL (childLH (childHH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childHH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childHH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111133311 :
    adaptiveCoverCheck 10 (childLH (childLH (childHH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childHH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childHH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111133312 :
    adaptiveCoverCheck 10 (childHL (childLH (childHH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLH (childHH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childHH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111133313 :
    adaptiveCoverCheck 10 (childHH (childLH (childHH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLH (childHH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childHH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111133320 :
    adaptiveCoverCheck 10 (childLL (childHL (childHH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHL (childHH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHL (childHH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111133321 :
    adaptiveCoverCheck 10 (childLH (childHL (childHH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHL (childHH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHL (childHH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111133322 :
    adaptiveCoverCheck 10 (childHL (childHL (childHH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHL (childHH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childHH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111133323 :
    adaptiveCoverCheck 10 (childHH (childHL (childHH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHL (childHH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childHH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111133330 :
    adaptiveCoverCheck 10 (childLL (childHH (childHH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHH (childHH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHH (childHH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111133331 :
    adaptiveCoverCheck 10 (childLH (childHH (childHH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHH (childHH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHH (childHH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111133332 :
    adaptiveCoverCheck 10 (childHL (childHH (childHH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHH (childHH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childHH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111133333 :
    adaptiveCoverCheck 10 (childHH (childHH (childHH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHH (childHH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childHH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1112000 :
    adaptiveCoverCheck 12 (childLL (childLL (childLL (childHL (childLH (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLL (childLL (childLL (childHL (childLH (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childLL (childHL (childLH (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1112001 :
    adaptiveCoverCheck 12 (childLH (childLL (childLL (childHL (childLH (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLH (childLL (childLL (childHL (childLH (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childLL (childHL (childLH (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1112002 :
    adaptiveCoverCheck 12 (childHL (childLL (childLL (childHL (childLH (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childHL (childLL (childLL (childHL (childLH (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL (childLL (childHL (childLH (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1112003 :
    adaptiveCoverCheck 12 (childHH (childLL (childLL (childHL (childLH (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childHH (childLL (childLL (childHL (childLH (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL (childLL (childHL (childLH (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1112010 :
    adaptiveCoverCheck 12 (childLL (childLH (childLL (childHL (childLH (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLL (childLH (childLL (childHL (childLH (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childLL (childHL (childLH (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1112011 :
    adaptiveCoverCheck 12 (childLH (childLH (childLL (childHL (childLH (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLH (childLH (childLL (childHL (childLH (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childLL (childHL (childLH (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1112012 :
    adaptiveCoverCheck 12 (childHL (childLH (childLL (childHL (childLH (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childHL (childLH (childLL (childHL (childLH (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childLL (childHL (childLH (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1112013 :
    adaptiveCoverCheck 12 (childHH (childLH (childLL (childHL (childLH (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childHH (childLH (childLL (childHL (childLH (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childLL (childHL (childLH (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111202 :
    adaptiveCoverCheck 13 (childHL (childLL (childHL (childLH (childLH (childLH e24ThetaAboveRoot)))))) = true := by
  have h : ((childHL (childLL (childHL (childLH (childLH (childLH e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLL (childHL (childLH (childLH (childLH e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111203 :
    adaptiveCoverCheck 13 (childHH (childLL (childHL (childLH (childLH (childLH e24ThetaAboveRoot)))))) = true := by
  have h : ((childHH (childLL (childHL (childLH (childLH (childLH e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLL (childHL (childLH (childLH (childLH e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1112100 :
    adaptiveCoverCheck 12 (childLL (childLL (childLH (childHL (childLH (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLL (childLL (childLH (childHL (childLH (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childLH (childHL (childLH (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1112101 :
    adaptiveCoverCheck 12 (childLH (childLL (childLH (childHL (childLH (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLH (childLL (childLH (childHL (childLH (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childLH (childHL (childLH (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1112102 :
    adaptiveCoverCheck 12 (childHL (childLL (childLH (childHL (childLH (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childHL (childLL (childLH (childHL (childLH (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL (childLH (childHL (childLH (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1112103 :
    adaptiveCoverCheck 12 (childHH (childLL (childLH (childHL (childLH (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childHH (childLL (childLH (childHL (childLH (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL (childLH (childHL (childLH (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1112110 :
    adaptiveCoverCheck 12 (childLL (childLH (childLH (childHL (childLH (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLL (childLH (childLH (childHL (childLH (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childLH (childHL (childLH (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1112111 :
    adaptiveCoverCheck 12 (childLH (childLH (childLH (childHL (childLH (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLH (childLH (childLH (childHL (childLH (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childLH (childHL (childLH (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1112112 :
    adaptiveCoverCheck 12 (childHL (childLH (childLH (childHL (childLH (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childHL (childLH (childLH (childHL (childLH (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childLH (childHL (childLH (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1112113 :
    adaptiveCoverCheck 12 (childHH (childLH (childLH (childHL (childLH (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childHH (childLH (childLH (childHL (childLH (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childLH (childHL (childLH (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111212 :
    adaptiveCoverCheck 13 (childHL (childLH (childHL (childLH (childLH (childLH e24ThetaAboveRoot)))))) = true := by
  have h : ((childHL (childLH (childHL (childLH (childLH (childLH e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLH (childHL (childLH (childLH (childLH e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111213 :
    adaptiveCoverCheck 13 (childHH (childLH (childHL (childLH (childLH (childLH e24ThetaAboveRoot)))))) = true := by
  have h : ((childHH (childLH (childHL (childLH (childLH (childLH e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLH (childHL (childLH (childLH (childLH e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11122 :
    adaptiveCoverCheck 14 (childHL (childHL (childLH (childLH (childLH e24ThetaAboveRoot))))) = true := by
  have h : ((childHL (childHL (childLH (childLH (childLH e24ThetaAboveRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 (childHL (childHL (childLH (childLH (childLH e24ThetaAboveRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11123 :
    adaptiveCoverCheck 14 (childHH (childHL (childLH (childLH (childLH e24ThetaAboveRoot))))) = true := by
  have h : ((childHH (childHL (childLH (childLH (childLH e24ThetaAboveRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 (childHH (childHL (childLH (childLH (childLH e24ThetaAboveRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1113000 :
    adaptiveCoverCheck 12 (childLL (childLL (childLL (childHH (childLH (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLL (childLL (childLL (childHH (childLH (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childLL (childHH (childLH (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1113001 :
    adaptiveCoverCheck 12 (childLH (childLL (childLL (childHH (childLH (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLH (childLL (childLL (childHH (childLH (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childLL (childHH (childLH (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1113002 :
    adaptiveCoverCheck 12 (childHL (childLL (childLL (childHH (childLH (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childHL (childLL (childLL (childHH (childLH (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL (childLL (childHH (childLH (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1113003 :
    adaptiveCoverCheck 12 (childHH (childLL (childLL (childHH (childLH (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childHH (childLL (childLL (childHH (childLH (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL (childLL (childHH (childLH (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1113010 :
    adaptiveCoverCheck 12 (childLL (childLH (childLL (childHH (childLH (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLL (childLH (childLL (childHH (childLH (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childLL (childHH (childLH (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1113011 :
    adaptiveCoverCheck 12 (childLH (childLH (childLL (childHH (childLH (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLH (childLH (childLL (childHH (childLH (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childLL (childHH (childLH (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1113012 :
    adaptiveCoverCheck 12 (childHL (childLH (childLL (childHH (childLH (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childHL (childLH (childLL (childHH (childLH (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childLL (childHH (childLH (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1113013 :
    adaptiveCoverCheck 12 (childHH (childLH (childLL (childHH (childLH (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childHH (childLH (childLL (childHH (childLH (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childLL (childHH (childLH (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111302 :
    adaptiveCoverCheck 13 (childHL (childLL (childHH (childLH (childLH (childLH e24ThetaAboveRoot)))))) = true := by
  have h : ((childHL (childLL (childHH (childLH (childLH (childLH e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLL (childHH (childLH (childLH (childLH e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111303 :
    adaptiveCoverCheck 13 (childHH (childLL (childHH (childLH (childLH (childLH e24ThetaAboveRoot)))))) = true := by
  have h : ((childHH (childLL (childHH (childLH (childLH (childLH e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLL (childHH (childLH (childLH (childLH e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1113100 :
    adaptiveCoverCheck 12 (childLL (childLL (childLH (childHH (childLH (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLL (childLL (childLH (childHH (childLH (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childLH (childHH (childLH (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1113101 :
    adaptiveCoverCheck 12 (childLH (childLL (childLH (childHH (childLH (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLH (childLL (childLH (childHH (childLH (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childLH (childHH (childLH (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1113102 :
    adaptiveCoverCheck 12 (childHL (childLL (childLH (childHH (childLH (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childHL (childLL (childLH (childHH (childLH (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL (childLH (childHH (childLH (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1113103 :
    adaptiveCoverCheck 12 (childHH (childLL (childLH (childHH (childLH (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childHH (childLL (childLH (childHH (childLH (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL (childLH (childHH (childLH (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1113110 :
    adaptiveCoverCheck 12 (childLL (childLH (childLH (childHH (childLH (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLL (childLH (childLH (childHH (childLH (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childLH (childHH (childLH (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1113111 :
    adaptiveCoverCheck 12 (childLH (childLH (childLH (childHH (childLH (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childLH (childLH (childLH (childHH (childLH (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childLH (childHH (childLH (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1113112 :
    adaptiveCoverCheck 12 (childHL (childLH (childLH (childHH (childLH (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childHL (childLH (childLH (childHH (childLH (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childLH (childHH (childLH (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1113113 :
    adaptiveCoverCheck 12 (childHH (childLH (childLH (childHH (childLH (childLH (childLH e24ThetaAboveRoot))))))) = true := by
  have h : ((childHH (childLH (childLH (childHH (childLH (childLH (childLH e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childLH (childHH (childLH (childLH (childLH e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111312 :
    adaptiveCoverCheck 13 (childHL (childLH (childHH (childLH (childLH (childLH e24ThetaAboveRoot)))))) = true := by
  have h : ((childHL (childLH (childHH (childLH (childLH (childLH e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLH (childHH (childLH (childLH (childLH e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf111313 :
    adaptiveCoverCheck 13 (childHH (childLH (childHH (childLH (childLH (childLH e24ThetaAboveRoot)))))) = true := by
  have h : ((childHH (childLH (childHH (childLH (childLH (childLH e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLH (childHH (childLH (childLH (childLH e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11132 :
    adaptiveCoverCheck 14 (childHL (childHH (childLH (childLH (childLH e24ThetaAboveRoot))))) = true := by
  have h : ((childHL (childHH (childLH (childLH (childLH e24ThetaAboveRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 (childHL (childHH (childLH (childLH (childLH e24ThetaAboveRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf11133 :
    adaptiveCoverCheck 14 (childHH (childHH (childLH (childLH (childLH e24ThetaAboveRoot))))) = true := by
  have h : ((childHH (childHH (childLH (childLH (childLH e24ThetaAboveRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 (childHH (childHH (childLH (childLH (childLH e24ThetaAboveRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1120 :
    adaptiveCoverCheck 15 (childLL (childHL (childLH (childLH e24ThetaAboveRoot)))) = true := by
  have h : ((childLL (childHL (childLH (childLH e24ThetaAboveRoot))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 (childLL (childHL (childLH (childLH e24ThetaAboveRoot)))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1121 :
    adaptiveCoverCheck 15 (childLH (childHL (childLH (childLH e24ThetaAboveRoot)))) = true := by
  have h : ((childLH (childHL (childLH (childLH e24ThetaAboveRoot))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 (childLH (childHL (childLH (childLH e24ThetaAboveRoot)))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1122 :
    adaptiveCoverCheck 15 (childHL (childHL (childLH (childLH e24ThetaAboveRoot)))) = true := by
  have h : ((childHL (childHL (childLH (childLH e24ThetaAboveRoot))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 (childHL (childHL (childLH (childLH e24ThetaAboveRoot)))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1123 :
    adaptiveCoverCheck 15 (childHH (childHL (childLH (childLH e24ThetaAboveRoot)))) = true := by
  have h : ((childHH (childHL (childLH (childLH e24ThetaAboveRoot))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 (childHH (childHL (childLH (childLH e24ThetaAboveRoot)))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1130 :
    adaptiveCoverCheck 15 (childLL (childHH (childLH (childLH e24ThetaAboveRoot)))) = true := by
  have h : ((childLL (childHH (childLH (childLH e24ThetaAboveRoot))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 (childLL (childHH (childLH (childLH e24ThetaAboveRoot)))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1131 :
    adaptiveCoverCheck 15 (childLH (childHH (childLH (childLH e24ThetaAboveRoot)))) = true := by
  have h : ((childLH (childHH (childLH (childLH e24ThetaAboveRoot))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 (childLH (childHH (childLH (childLH e24ThetaAboveRoot)))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1132 :
    adaptiveCoverCheck 15 (childHL (childHH (childLH (childLH e24ThetaAboveRoot)))) = true := by
  have h : ((childHL (childHH (childLH (childLH e24ThetaAboveRoot))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 (childHL (childHH (childLH (childLH e24ThetaAboveRoot)))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf1133 :
    adaptiveCoverCheck 15 (childHH (childHH (childLH (childLH e24ThetaAboveRoot)))) = true := by
  have h : ((childHH (childHH (childLH (childLH e24ThetaAboveRoot))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 (childHH (childHH (childLH (childLH e24ThetaAboveRoot)))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf120 :
    adaptiveCoverCheck 16 (childLL (childHL (childLH e24ThetaAboveRoot))) = true := by
  have h : ((childLL (childHL (childLH e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childLL (childHL (childLH e24ThetaAboveRoot))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf121 :
    adaptiveCoverCheck 16 (childLH (childHL (childLH e24ThetaAboveRoot))) = true := by
  have h : ((childLH (childHL (childLH e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childLH (childHL (childLH e24ThetaAboveRoot))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf122 :
    adaptiveCoverCheck 16 (childHL (childHL (childLH e24ThetaAboveRoot))) = true := by
  have h : ((childHL (childHL (childLH e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childHL (childHL (childLH e24ThetaAboveRoot))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf123 :
    adaptiveCoverCheck 16 (childHH (childHL (childLH e24ThetaAboveRoot))) = true := by
  have h : ((childHH (childHL (childLH e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childHH (childHL (childLH e24ThetaAboveRoot))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf130 :
    adaptiveCoverCheck 16 (childLL (childHH (childLH e24ThetaAboveRoot))) = true := by
  have h : ((childLL (childHH (childLH e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childLL (childHH (childLH e24ThetaAboveRoot))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf131 :
    adaptiveCoverCheck 16 (childLH (childHH (childLH e24ThetaAboveRoot))) = true := by
  have h : ((childLH (childHH (childLH e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childLH (childHH (childLH e24ThetaAboveRoot))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf132 :
    adaptiveCoverCheck 16 (childHL (childHH (childLH e24ThetaAboveRoot))) = true := by
  have h : ((childHL (childHH (childLH e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childHL (childHH (childLH e24ThetaAboveRoot))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf133 :
    adaptiveCoverCheck 16 (childHH (childHH (childLH e24ThetaAboveRoot))) = true := by
  have h : ((childHH (childHH (childLH e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childHH (childHH (childLH e24ThetaAboveRoot))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf200 :
    adaptiveCoverCheck 16 (childLL (childLL (childHL e24ThetaAboveRoot))) = true := by
  have h : ((childLL (childLL (childHL e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childLL (childLL (childHL e24ThetaAboveRoot))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf201 :
    adaptiveCoverCheck 16 (childLH (childLL (childHL e24ThetaAboveRoot))) = true := by
  have h : ((childLH (childLL (childHL e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childLH (childLL (childHL e24ThetaAboveRoot))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf202 :
    adaptiveCoverCheck 16 (childHL (childLL (childHL e24ThetaAboveRoot))) = true := by
  have h : ((childHL (childLL (childHL e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childHL (childLL (childHL e24ThetaAboveRoot))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf203 :
    adaptiveCoverCheck 16 (childHH (childLL (childHL e24ThetaAboveRoot))) = true := by
  have h : ((childHH (childLL (childHL e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childHH (childLL (childHL e24ThetaAboveRoot))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf210 :
    adaptiveCoverCheck 16 (childLL (childLH (childHL e24ThetaAboveRoot))) = true := by
  have h : ((childLL (childLH (childHL e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childLL (childLH (childHL e24ThetaAboveRoot))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf211 :
    adaptiveCoverCheck 16 (childLH (childLH (childHL e24ThetaAboveRoot))) = true := by
  have h : ((childLH (childLH (childHL e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childLH (childLH (childHL e24ThetaAboveRoot))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf212 :
    adaptiveCoverCheck 16 (childHL (childLH (childHL e24ThetaAboveRoot))) = true := by
  have h : ((childHL (childLH (childHL e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childHL (childLH (childHL e24ThetaAboveRoot))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf213 :
    adaptiveCoverCheck 16 (childHH (childLH (childHL e24ThetaAboveRoot))) = true := by
  have h : ((childHH (childLH (childHL e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childHH (childLH (childHL e24ThetaAboveRoot))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf220 :
    adaptiveCoverCheck 16 (childLL (childHL (childHL e24ThetaAboveRoot))) = true := by
  have h : ((childLL (childHL (childHL e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childLL (childHL (childHL e24ThetaAboveRoot))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf221 :
    adaptiveCoverCheck 16 (childLH (childHL (childHL e24ThetaAboveRoot))) = true := by
  have h : ((childLH (childHL (childHL e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childLH (childHL (childHL e24ThetaAboveRoot))) h

theorem e24KC2ThetaAboveLeaf222 :
    adaptiveCoverCheck 16 (childHL (childHL (childHL e24ThetaAboveRoot))) = true := by
  have h : physicallyIrrelevant (childHL (childHL (childHL e24ThetaAboveRoot))) = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_physicallyIrrelevant 16 (childHL (childHL (childHL e24ThetaAboveRoot))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf223 :
    adaptiveCoverCheck 16 (childHH (childHL (childHL e24ThetaAboveRoot))) = true := by
  have h : ((childHH (childHL (childHL e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childHH (childHL (childHL e24ThetaAboveRoot))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf230 :
    adaptiveCoverCheck 16 (childLL (childHH (childHL e24ThetaAboveRoot))) = true := by
  have h : ((childLL (childHH (childHL e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childLL (childHH (childHL e24ThetaAboveRoot))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf231 :
    adaptiveCoverCheck 16 (childLH (childHH (childHL e24ThetaAboveRoot))) = true := by
  have h : ((childLH (childHH (childHL e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childLH (childHH (childHL e24ThetaAboveRoot))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf232 :
    adaptiveCoverCheck 16 (childHL (childHH (childHL e24ThetaAboveRoot))) = true := by
  have h : ((childHL (childHH (childHL e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childHL (childHH (childHL e24ThetaAboveRoot))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf233 :
    adaptiveCoverCheck 16 (childHH (childHH (childHL e24ThetaAboveRoot))) = true := by
  have h : ((childHH (childHH (childHL e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childHH (childHH (childHL e24ThetaAboveRoot))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf300 :
    adaptiveCoverCheck 16 (childLL (childLL (childHH e24ThetaAboveRoot))) = true := by
  have h : ((childLL (childLL (childHH e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childLL (childLL (childHH e24ThetaAboveRoot))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf301 :
    adaptiveCoverCheck 16 (childLH (childLL (childHH e24ThetaAboveRoot))) = true := by
  have h : ((childLH (childLL (childHH e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childLH (childLL (childHH e24ThetaAboveRoot))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf302 :
    adaptiveCoverCheck 16 (childHL (childLL (childHH e24ThetaAboveRoot))) = true := by
  have h : ((childHL (childLL (childHH e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childHL (childLL (childHH e24ThetaAboveRoot))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf303 :
    adaptiveCoverCheck 16 (childHH (childLL (childHH e24ThetaAboveRoot))) = true := by
  have h : ((childHH (childLL (childHH e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childHH (childLL (childHH e24ThetaAboveRoot))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf310 :
    adaptiveCoverCheck 16 (childLL (childLH (childHH e24ThetaAboveRoot))) = true := by
  have h : ((childLL (childLH (childHH e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childLL (childLH (childHH e24ThetaAboveRoot))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf311 :
    adaptiveCoverCheck 16 (childLH (childLH (childHH e24ThetaAboveRoot))) = true := by
  have h : ((childLH (childLH (childHH e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childLH (childLH (childHH e24ThetaAboveRoot))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf312 :
    adaptiveCoverCheck 16 (childHL (childLH (childHH e24ThetaAboveRoot))) = true := by
  have h : ((childHL (childLH (childHH e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childHL (childLH (childHH e24ThetaAboveRoot))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf313 :
    adaptiveCoverCheck 16 (childHH (childLH (childHH e24ThetaAboveRoot))) = true := by
  have h : ((childHH (childLH (childHH e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childHH (childLH (childHH e24ThetaAboveRoot))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf320 :
    adaptiveCoverCheck 16 (childLL (childHL (childHH e24ThetaAboveRoot))) = true := by
  have h : ((childLL (childHL (childHH e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childLL (childHL (childHH e24ThetaAboveRoot))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf321 :
    adaptiveCoverCheck 16 (childLH (childHL (childHH e24ThetaAboveRoot))) = true := by
  have h : ((childLH (childHL (childHH e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childLH (childHL (childHH e24ThetaAboveRoot))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf322 :
    adaptiveCoverCheck 16 (childHL (childHL (childHH e24ThetaAboveRoot))) = true := by
  have h : ((childHL (childHL (childHH e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childHL (childHL (childHH e24ThetaAboveRoot))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf323 :
    adaptiveCoverCheck 16 (childHH (childHL (childHH e24ThetaAboveRoot))) = true := by
  have h : ((childHH (childHL (childHH e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childHH (childHL (childHH e24ThetaAboveRoot))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf330 :
    adaptiveCoverCheck 16 (childLL (childHH (childHH e24ThetaAboveRoot))) = true := by
  have h : ((childLL (childHH (childHH e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childLL (childHH (childHH e24ThetaAboveRoot))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf331 :
    adaptiveCoverCheck 16 (childLH (childHH (childHH e24ThetaAboveRoot))) = true := by
  have h : ((childLH (childHH (childHH e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childLH (childHH (childHH e24ThetaAboveRoot))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf332 :
    adaptiveCoverCheck 16 (childHL (childHH (childHH e24ThetaAboveRoot))) = true := by
  have h : ((childHL (childHH (childHH e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childHL (childHH (childHH e24ThetaAboveRoot))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf333 :
    adaptiveCoverCheck 16 (childHH (childHH (childHH e24ThetaAboveRoot))) = true := by
  have h : ((childHH (childHH (childHH e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childHH (childHH (childHH e24ThetaAboveRoot))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf0000 :
    adaptiveCoverCheck 14 (childLL (childLL (childLL (childLL e24ThetaBelowRoot)))) = true := by
  have h : ((childLL (childLL (childLL (childLL e24ThetaBelowRoot))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 (childLL (childLL (childLL (childLL e24ThetaBelowRoot)))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf0001 :
    adaptiveCoverCheck 14 (childLH (childLL (childLL (childLL e24ThetaBelowRoot)))) = true := by
  have h : ((childLH (childLL (childLL (childLL e24ThetaBelowRoot))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 (childLH (childLL (childLL (childLL e24ThetaBelowRoot)))) h

theorem e24KC2ThetaBelowLeaf0002 :
    adaptiveCoverCheck 14 (childHL (childLL (childLL (childLL e24ThetaBelowRoot)))) = true := by
  have h : physicallyIrrelevant (childHL (childLL (childLL (childLL e24ThetaBelowRoot)))) = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_physicallyIrrelevant 14 (childHL (childLL (childLL (childLL e24ThetaBelowRoot)))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf00030 :
    adaptiveCoverCheck 13 (childLL (childHH (childLL (childLL (childLL e24ThetaBelowRoot))))) = true := by
  have h : ((childLL (childHH (childLL (childLL (childLL e24ThetaBelowRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL (childHH (childLL (childLL (childLL e24ThetaBelowRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf00031 :
    adaptiveCoverCheck 13 (childLH (childHH (childLL (childLL (childLL e24ThetaBelowRoot))))) = true := by
  have h : ((childLH (childHH (childLL (childLL (childLL e24ThetaBelowRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH (childHH (childLL (childLL (childLL e24ThetaBelowRoot))))) h

theorem e24KC2ThetaBelowLeaf00032 :
    adaptiveCoverCheck 13 (childHL (childHH (childLL (childLL (childLL e24ThetaBelowRoot))))) = true := by
  have h : physicallyIrrelevant (childHL (childHH (childLL (childLL (childLL e24ThetaBelowRoot))))) = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_physicallyIrrelevant 13 (childHL (childHH (childLL (childLL (childLL e24ThetaBelowRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf00033 :
    adaptiveCoverCheck 13 (childHH (childHH (childLL (childLL (childLL e24ThetaBelowRoot))))) = true := by
  have h : ((childHH (childHH (childLL (childLL (childLL e24ThetaBelowRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childHH (childLL (childLL (childLL e24ThetaBelowRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf00100 :
    adaptiveCoverCheck 13 (childLL (childLL (childLH (childLL (childLL e24ThetaBelowRoot))))) = true := by
  have h : ((childLL (childLL (childLH (childLL (childLL e24ThetaBelowRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL (childLL (childLH (childLL (childLL e24ThetaBelowRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf00101 :
    adaptiveCoverCheck 13 (childLH (childLL (childLH (childLL (childLL e24ThetaBelowRoot))))) = true := by
  have h : ((childLH (childLL (childLH (childLL (childLL e24ThetaBelowRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH (childLL (childLH (childLL (childLL e24ThetaBelowRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf00102 :
    adaptiveCoverCheck 13 (childHL (childLL (childLH (childLL (childLL e24ThetaBelowRoot))))) = true := by
  have h : ((childHL (childLL (childLH (childLL (childLL e24ThetaBelowRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLL (childLH (childLL (childLL e24ThetaBelowRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf00103 :
    adaptiveCoverCheck 13 (childHH (childLL (childLH (childLL (childLL e24ThetaBelowRoot))))) = true := by
  have h : ((childHH (childLL (childLH (childLL (childLL e24ThetaBelowRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLL (childLH (childLL (childLL e24ThetaBelowRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf00110 :
    adaptiveCoverCheck 13 (childLL (childLH (childLH (childLL (childLL e24ThetaBelowRoot))))) = true := by
  have h : ((childLL (childLH (childLH (childLL (childLL e24ThetaBelowRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL (childLH (childLH (childLL (childLL e24ThetaBelowRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf00111 :
    adaptiveCoverCheck 13 (childLH (childLH (childLH (childLL (childLL e24ThetaBelowRoot))))) = true := by
  have h : ((childLH (childLH (childLH (childLL (childLL e24ThetaBelowRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH (childLH (childLH (childLL (childLL e24ThetaBelowRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf00112 :
    adaptiveCoverCheck 13 (childHL (childLH (childLH (childLL (childLL e24ThetaBelowRoot))))) = true := by
  have h : ((childHL (childLH (childLH (childLL (childLL e24ThetaBelowRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLH (childLH (childLL (childLL e24ThetaBelowRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf00113 :
    adaptiveCoverCheck 13 (childHH (childLH (childLH (childLL (childLL e24ThetaBelowRoot))))) = true := by
  have h : ((childHH (childLH (childLH (childLL (childLL e24ThetaBelowRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLH (childLH (childLL (childLL e24ThetaBelowRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf00120 :
    adaptiveCoverCheck 13 (childLL (childHL (childLH (childLL (childLL e24ThetaBelowRoot))))) = true := by
  have h : ((childLL (childHL (childLH (childLL (childLL e24ThetaBelowRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL (childHL (childLH (childLL (childLL e24ThetaBelowRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf00121 :
    adaptiveCoverCheck 13 (childLH (childHL (childLH (childLL (childLL e24ThetaBelowRoot))))) = true := by
  have h : ((childLH (childHL (childLH (childLL (childLL e24ThetaBelowRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH (childHL (childLH (childLL (childLL e24ThetaBelowRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf00122 :
    adaptiveCoverCheck 13 (childHL (childHL (childLH (childLL (childLL e24ThetaBelowRoot))))) = true := by
  have h : ((childHL (childHL (childLH (childLL (childLL e24ThetaBelowRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childHL (childLH (childLL (childLL e24ThetaBelowRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf00123 :
    adaptiveCoverCheck 13 (childHH (childHL (childLH (childLL (childLL e24ThetaBelowRoot))))) = true := by
  have h : ((childHH (childHL (childLH (childLL (childLL e24ThetaBelowRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childHL (childLH (childLL (childLL e24ThetaBelowRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf00130 :
    adaptiveCoverCheck 13 (childLL (childHH (childLH (childLL (childLL e24ThetaBelowRoot))))) = true := by
  have h : ((childLL (childHH (childLH (childLL (childLL e24ThetaBelowRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL (childHH (childLH (childLL (childLL e24ThetaBelowRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf00131 :
    adaptiveCoverCheck 13 (childLH (childHH (childLH (childLL (childLL e24ThetaBelowRoot))))) = true := by
  have h : ((childLH (childHH (childLH (childLL (childLL e24ThetaBelowRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH (childHH (childLH (childLL (childLL e24ThetaBelowRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf00132 :
    adaptiveCoverCheck 13 (childHL (childHH (childLH (childLL (childLL e24ThetaBelowRoot))))) = true := by
  have h : ((childHL (childHH (childLH (childLL (childLL e24ThetaBelowRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childHH (childLH (childLL (childLL e24ThetaBelowRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf00133 :
    adaptiveCoverCheck 13 (childHH (childHH (childLH (childLL (childLL e24ThetaBelowRoot))))) = true := by
  have h : ((childHH (childHH (childLH (childLL (childLL e24ThetaBelowRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childHH (childLH (childLL (childLL e24ThetaBelowRoot))))) h

theorem e24KC2ThetaBelowLeaf002 :
    adaptiveCoverCheck 15 (childHL (childLL (childLL e24ThetaBelowRoot))) = true := by
  have h : physicallyIrrelevant (childHL (childLL (childLL e24ThetaBelowRoot))) = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_physicallyIrrelevant 15 (childHL (childLL (childLL e24ThetaBelowRoot))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf0030 :
    adaptiveCoverCheck 14 (childLL (childHH (childLL (childLL e24ThetaBelowRoot)))) = true := by
  have h : ((childLL (childHH (childLL (childLL e24ThetaBelowRoot))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 (childLL (childHH (childLL (childLL e24ThetaBelowRoot)))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf0031 :
    adaptiveCoverCheck 14 (childLH (childHH (childLL (childLL e24ThetaBelowRoot)))) = true := by
  have h : ((childLH (childHH (childLL (childLL e24ThetaBelowRoot))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 (childLH (childHH (childLL (childLL e24ThetaBelowRoot)))) h

theorem e24KC2ThetaBelowLeaf0032 :
    adaptiveCoverCheck 14 (childHL (childHH (childLL (childLL e24ThetaBelowRoot)))) = true := by
  have h : physicallyIrrelevant (childHL (childHH (childLL (childLL e24ThetaBelowRoot)))) = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_physicallyIrrelevant 14 (childHL (childHH (childLL (childLL e24ThetaBelowRoot)))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf0033 :
    adaptiveCoverCheck 14 (childHH (childHH (childLL (childLL e24ThetaBelowRoot)))) = true := by
  have h : ((childHH (childHH (childLL (childLL e24ThetaBelowRoot))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 (childHH (childHH (childLL (childLL e24ThetaBelowRoot)))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf01000 :
    adaptiveCoverCheck 13 (childLL (childLL (childLL (childLH (childLL e24ThetaBelowRoot))))) = true := by
  have h : ((childLL (childLL (childLL (childLH (childLL e24ThetaBelowRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL (childLL (childLL (childLH (childLL e24ThetaBelowRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf01001 :
    adaptiveCoverCheck 13 (childLH (childLL (childLL (childLH (childLL e24ThetaBelowRoot))))) = true := by
  have h : ((childLH (childLL (childLL (childLH (childLL e24ThetaBelowRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH (childLL (childLL (childLH (childLL e24ThetaBelowRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf01002 :
    adaptiveCoverCheck 13 (childHL (childLL (childLL (childLH (childLL e24ThetaBelowRoot))))) = true := by
  have h : ((childHL (childLL (childLL (childLH (childLL e24ThetaBelowRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLL (childLL (childLH (childLL e24ThetaBelowRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf01003 :
    adaptiveCoverCheck 13 (childHH (childLL (childLL (childLH (childLL e24ThetaBelowRoot))))) = true := by
  have h : ((childHH (childLL (childLL (childLH (childLL e24ThetaBelowRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLL (childLL (childLH (childLL e24ThetaBelowRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf01010 :
    adaptiveCoverCheck 13 (childLL (childLH (childLL (childLH (childLL e24ThetaBelowRoot))))) = true := by
  have h : ((childLL (childLH (childLL (childLH (childLL e24ThetaBelowRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL (childLH (childLL (childLH (childLL e24ThetaBelowRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf01011 :
    adaptiveCoverCheck 13 (childLH (childLH (childLL (childLH (childLL e24ThetaBelowRoot))))) = true := by
  have h : ((childLH (childLH (childLL (childLH (childLL e24ThetaBelowRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH (childLH (childLL (childLH (childLL e24ThetaBelowRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf01012 :
    adaptiveCoverCheck 13 (childHL (childLH (childLL (childLH (childLL e24ThetaBelowRoot))))) = true := by
  have h : ((childHL (childLH (childLL (childLH (childLL e24ThetaBelowRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLH (childLL (childLH (childLL e24ThetaBelowRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf010130 :
    adaptiveCoverCheck 12 (childLL (childHH (childLH (childLL (childLH (childLL e24ThetaBelowRoot)))))) = true := by
  have h : ((childLL (childHH (childLH (childLL (childLH (childLL e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childHH (childLH (childLL (childLH (childLL e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf010131 :
    adaptiveCoverCheck 12 (childLH (childHH (childLH (childLL (childLH (childLL e24ThetaBelowRoot)))))) = true := by
  have h : ((childLH (childHH (childLH (childLL (childLH (childLL e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childHH (childLH (childLL (childLH (childLL e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf010132 :
    adaptiveCoverCheck 12 (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaBelowRoot)))))) = true := by
  have h : ((childHL (childHH (childLH (childLL (childLH (childLL e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childHH (childLH (childLL (childLH (childLL e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf010133 :
    adaptiveCoverCheck 12 (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaBelowRoot)))))) = true := by
  have h : ((childHH (childHH (childLH (childLL (childLH (childLL e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childHH (childLH (childLL (childLH (childLL e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf01020 :
    adaptiveCoverCheck 13 (childLL (childHL (childLL (childLH (childLL e24ThetaBelowRoot))))) = true := by
  have h : ((childLL (childHL (childLL (childLH (childLL e24ThetaBelowRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL (childHL (childLL (childLH (childLL e24ThetaBelowRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf01021 :
    adaptiveCoverCheck 13 (childLH (childHL (childLL (childLH (childLL e24ThetaBelowRoot))))) = true := by
  have h : ((childLH (childHL (childLL (childLH (childLL e24ThetaBelowRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH (childHL (childLL (childLH (childLL e24ThetaBelowRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf01022 :
    adaptiveCoverCheck 13 (childHL (childHL (childLL (childLH (childLL e24ThetaBelowRoot))))) = true := by
  have h : ((childHL (childHL (childLL (childLH (childLL e24ThetaBelowRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childHL (childLL (childLH (childLL e24ThetaBelowRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf01023 :
    adaptiveCoverCheck 13 (childHH (childHL (childLL (childLH (childLL e24ThetaBelowRoot))))) = true := by
  have h : ((childHH (childHL (childLL (childLH (childLL e24ThetaBelowRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childHL (childLL (childLH (childLL e24ThetaBelowRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf01030 :
    adaptiveCoverCheck 13 (childLL (childHH (childLL (childLH (childLL e24ThetaBelowRoot))))) = true := by
  have h : ((childLL (childHH (childLL (childLH (childLL e24ThetaBelowRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL (childHH (childLL (childLH (childLL e24ThetaBelowRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf01031 :
    adaptiveCoverCheck 13 (childLH (childHH (childLL (childLH (childLL e24ThetaBelowRoot))))) = true := by
  have h : ((childLH (childHH (childLL (childLH (childLL e24ThetaBelowRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH (childHH (childLL (childLH (childLL e24ThetaBelowRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf01032 :
    adaptiveCoverCheck 13 (childHL (childHH (childLL (childLH (childLL e24ThetaBelowRoot))))) = true := by
  have h : ((childHL (childHH (childLL (childLH (childLL e24ThetaBelowRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childHH (childLL (childLH (childLL e24ThetaBelowRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf01033 :
    adaptiveCoverCheck 13 (childHH (childHH (childLL (childLH (childLL e24ThetaBelowRoot))))) = true := by
  have h : ((childHH (childHH (childLL (childLH (childLL e24ThetaBelowRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childHH (childLL (childLH (childLL e24ThetaBelowRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf01100 :
    adaptiveCoverCheck 13 (childLL (childLL (childLH (childLH (childLL e24ThetaBelowRoot))))) = true := by
  have h : ((childLL (childLL (childLH (childLH (childLL e24ThetaBelowRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL (childLL (childLH (childLH (childLL e24ThetaBelowRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf011010 :
    adaptiveCoverCheck 12 (childLL (childLH (childLL (childLH (childLH (childLL e24ThetaBelowRoot)))))) = true := by
  have h : ((childLL (childLH (childLL (childLH (childLH (childLL e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childLL (childLH (childLH (childLL e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf011011 :
    adaptiveCoverCheck 12 (childLH (childLH (childLL (childLH (childLH (childLL e24ThetaBelowRoot)))))) = true := by
  have h : ((childLH (childLH (childLL (childLH (childLH (childLL e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childLL (childLH (childLH (childLL e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf011012 :
    adaptiveCoverCheck 12 (childHL (childLH (childLL (childLH (childLH (childLL e24ThetaBelowRoot)))))) = true := by
  have h : ((childHL (childLH (childLL (childLH (childLH (childLL e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childLL (childLH (childLH (childLL e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf011013 :
    adaptiveCoverCheck 12 (childHH (childLH (childLL (childLH (childLH (childLL e24ThetaBelowRoot)))))) = true := by
  have h : ((childHH (childLH (childLL (childLH (childLH (childLL e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childLL (childLH (childLH (childLL e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf011020 :
    adaptiveCoverCheck 12 (childLL (childHL (childLL (childLH (childLH (childLL e24ThetaBelowRoot)))))) = true := by
  have h : ((childLL (childHL (childLL (childLH (childLH (childLL e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childHL (childLL (childLH (childLH (childLL e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf011021 :
    adaptiveCoverCheck 12 (childLH (childHL (childLL (childLH (childLH (childLL e24ThetaBelowRoot)))))) = true := by
  have h : ((childLH (childHL (childLL (childLH (childLH (childLL e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childHL (childLL (childLH (childLH (childLL e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf011022 :
    adaptiveCoverCheck 12 (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaBelowRoot)))))) = true := by
  have h : ((childHL (childHL (childLL (childLH (childLH (childLL e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childHL (childLL (childLH (childLH (childLL e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf011023 :
    adaptiveCoverCheck 12 (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaBelowRoot)))))) = true := by
  have h : ((childHH (childHL (childLL (childLH (childLH (childLL e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childHL (childLL (childLH (childLH (childLL e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf011030 :
    adaptiveCoverCheck 12 (childLL (childHH (childLL (childLH (childLH (childLL e24ThetaBelowRoot)))))) = true := by
  have h : ((childLL (childHH (childLL (childLH (childLH (childLL e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childHH (childLL (childLH (childLH (childLL e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf011031 :
    adaptiveCoverCheck 12 (childLH (childHH (childLL (childLH (childLH (childLL e24ThetaBelowRoot)))))) = true := by
  have h : ((childLH (childHH (childLL (childLH (childLH (childLL e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childHH (childLL (childLH (childLH (childLL e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf011032 :
    adaptiveCoverCheck 12 (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaBelowRoot)))))) = true := by
  have h : ((childHL (childHH (childLL (childLH (childLH (childLL e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf011033 :
    adaptiveCoverCheck 12 (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaBelowRoot)))))) = true := by
  have h : ((childHH (childHH (childLL (childLH (childLH (childLL e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf011100 :
    adaptiveCoverCheck 12 (childLL (childLL (childLH (childLH (childLH (childLL e24ThetaBelowRoot)))))) = true := by
  have h : ((childLL (childLL (childLH (childLH (childLH (childLL e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childLH (childLH (childLH (childLL e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf011101 :
    adaptiveCoverCheck 12 (childLH (childLL (childLH (childLH (childLH (childLL e24ThetaBelowRoot)))))) = true := by
  have h : ((childLH (childLL (childLH (childLH (childLH (childLL e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childLH (childLH (childLH (childLL e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf011102 :
    adaptiveCoverCheck 12 (childHL (childLL (childLH (childLH (childLH (childLL e24ThetaBelowRoot)))))) = true := by
  have h : ((childHL (childLL (childLH (childLH (childLH (childLL e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL (childLH (childLH (childLH (childLL e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf011103 :
    adaptiveCoverCheck 12 (childHH (childLL (childLH (childLH (childLH (childLL e24ThetaBelowRoot)))))) = true := by
  have h : ((childHH (childLL (childLH (childLH (childLH (childLL e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL (childLH (childLH (childLH (childLL e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf011110 :
    adaptiveCoverCheck 12 (childLL (childLH (childLH (childLH (childLH (childLL e24ThetaBelowRoot)))))) = true := by
  have h : ((childLL (childLH (childLH (childLH (childLH (childLL e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childLH (childLH (childLH (childLL e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf011111 :
    adaptiveCoverCheck 12 (childLH (childLH (childLH (childLH (childLH (childLL e24ThetaBelowRoot)))))) = true := by
  have h : ((childLH (childLH (childLH (childLH (childLH (childLL e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childLH (childLH (childLH (childLL e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf011112 :
    adaptiveCoverCheck 12 (childHL (childLH (childLH (childLH (childLH (childLL e24ThetaBelowRoot)))))) = true := by
  have h : ((childHL (childLH (childLH (childLH (childLH (childLL e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childLH (childLH (childLH (childLL e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf011113 :
    adaptiveCoverCheck 12 (childHH (childLH (childLH (childLH (childLH (childLL e24ThetaBelowRoot)))))) = true := by
  have h : ((childHH (childLH (childLH (childLH (childLH (childLL e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childLH (childLH (childLH (childLL e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf011120 :
    adaptiveCoverCheck 12 (childLL (childHL (childLH (childLH (childLH (childLL e24ThetaBelowRoot)))))) = true := by
  have h : ((childLL (childHL (childLH (childLH (childLH (childLL e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childHL (childLH (childLH (childLH (childLL e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf011121 :
    adaptiveCoverCheck 12 (childLH (childHL (childLH (childLH (childLH (childLL e24ThetaBelowRoot)))))) = true := by
  have h : ((childLH (childHL (childLH (childLH (childLH (childLL e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childHL (childLH (childLH (childLH (childLL e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf011122 :
    adaptiveCoverCheck 12 (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaBelowRoot)))))) = true := by
  have h : ((childHL (childHL (childLH (childLH (childLH (childLL e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf011123 :
    adaptiveCoverCheck 12 (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaBelowRoot)))))) = true := by
  have h : ((childHH (childHL (childLH (childLH (childLH (childLL e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf011130 :
    adaptiveCoverCheck 12 (childLL (childHH (childLH (childLH (childLH (childLL e24ThetaBelowRoot)))))) = true := by
  have h : ((childLL (childHH (childLH (childLH (childLH (childLL e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childHH (childLH (childLH (childLH (childLL e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf011131 :
    adaptiveCoverCheck 12 (childLH (childHH (childLH (childLH (childLH (childLL e24ThetaBelowRoot)))))) = true := by
  have h : ((childLH (childHH (childLH (childLH (childLH (childLL e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childHH (childLH (childLH (childLH (childLL e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf011132 :
    adaptiveCoverCheck 12 (childHL (childHH (childLH (childLH (childLH (childLL e24ThetaBelowRoot)))))) = true := by
  have h : ((childHL (childHH (childLH (childLH (childLH (childLL e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childHH (childLH (childLH (childLH (childLL e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf011133 :
    adaptiveCoverCheck 12 (childHH (childHH (childLH (childLH (childLH (childLL e24ThetaBelowRoot)))))) = true := by
  have h : ((childHH (childHH (childLH (childLH (childLH (childLL e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childHH (childLH (childLH (childLH (childLL e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf01120 :
    adaptiveCoverCheck 13 (childLL (childHL (childLH (childLH (childLL e24ThetaBelowRoot))))) = true := by
  have h : ((childLL (childHL (childLH (childLH (childLL e24ThetaBelowRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL (childHL (childLH (childLH (childLL e24ThetaBelowRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf01121 :
    adaptiveCoverCheck 13 (childLH (childHL (childLH (childLH (childLL e24ThetaBelowRoot))))) = true := by
  have h : ((childLH (childHL (childLH (childLH (childLL e24ThetaBelowRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH (childHL (childLH (childLH (childLL e24ThetaBelowRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf01122 :
    adaptiveCoverCheck 13 (childHL (childHL (childLH (childLH (childLL e24ThetaBelowRoot))))) = true := by
  have h : ((childHL (childHL (childLH (childLH (childLL e24ThetaBelowRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childHL (childLH (childLH (childLL e24ThetaBelowRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf01123 :
    adaptiveCoverCheck 13 (childHH (childHL (childLH (childLH (childLL e24ThetaBelowRoot))))) = true := by
  have h : ((childHH (childHL (childLH (childLH (childLL e24ThetaBelowRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childHL (childLH (childLH (childLL e24ThetaBelowRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf01130 :
    adaptiveCoverCheck 13 (childLL (childHH (childLH (childLH (childLL e24ThetaBelowRoot))))) = true := by
  have h : ((childLL (childHH (childLH (childLH (childLL e24ThetaBelowRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL (childHH (childLH (childLH (childLL e24ThetaBelowRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf01131 :
    adaptiveCoverCheck 13 (childLH (childHH (childLH (childLH (childLL e24ThetaBelowRoot))))) = true := by
  have h : ((childLH (childHH (childLH (childLH (childLL e24ThetaBelowRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH (childHH (childLH (childLH (childLL e24ThetaBelowRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf01132 :
    adaptiveCoverCheck 13 (childHL (childHH (childLH (childLH (childLL e24ThetaBelowRoot))))) = true := by
  have h : ((childHL (childHH (childLH (childLH (childLL e24ThetaBelowRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childHH (childLH (childLH (childLL e24ThetaBelowRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf01133 :
    adaptiveCoverCheck 13 (childHH (childHH (childLH (childLH (childLL e24ThetaBelowRoot))))) = true := by
  have h : ((childHH (childHH (childLH (childLH (childLL e24ThetaBelowRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childHH (childLH (childLH (childLL e24ThetaBelowRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf0120 :
    adaptiveCoverCheck 14 (childLL (childHL (childLH (childLL e24ThetaBelowRoot)))) = true := by
  have h : ((childLL (childHL (childLH (childLL e24ThetaBelowRoot))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 (childLL (childHL (childLH (childLL e24ThetaBelowRoot)))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf0121 :
    adaptiveCoverCheck 14 (childLH (childHL (childLH (childLL e24ThetaBelowRoot)))) = true := by
  have h : ((childLH (childHL (childLH (childLL e24ThetaBelowRoot))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 (childLH (childHL (childLH (childLL e24ThetaBelowRoot)))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf0122 :
    adaptiveCoverCheck 14 (childHL (childHL (childLH (childLL e24ThetaBelowRoot)))) = true := by
  have h : ((childHL (childHL (childLH (childLL e24ThetaBelowRoot))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 (childHL (childHL (childLH (childLL e24ThetaBelowRoot)))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf0123 :
    adaptiveCoverCheck 14 (childHH (childHL (childLH (childLL e24ThetaBelowRoot)))) = true := by
  have h : ((childHH (childHL (childLH (childLL e24ThetaBelowRoot))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 (childHH (childHL (childLH (childLL e24ThetaBelowRoot)))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf0130 :
    adaptiveCoverCheck 14 (childLL (childHH (childLH (childLL e24ThetaBelowRoot)))) = true := by
  have h : ((childLL (childHH (childLH (childLL e24ThetaBelowRoot))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 (childLL (childHH (childLH (childLL e24ThetaBelowRoot)))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf0131 :
    adaptiveCoverCheck 14 (childLH (childHH (childLH (childLL e24ThetaBelowRoot)))) = true := by
  have h : ((childLH (childHH (childLH (childLL e24ThetaBelowRoot))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 (childLH (childHH (childLH (childLL e24ThetaBelowRoot)))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf0132 :
    adaptiveCoverCheck 14 (childHL (childHH (childLH (childLL e24ThetaBelowRoot)))) = true := by
  have h : ((childHL (childHH (childLH (childLL e24ThetaBelowRoot))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 (childHL (childHH (childLH (childLL e24ThetaBelowRoot)))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf0133 :
    adaptiveCoverCheck 14 (childHH (childHH (childLH (childLL e24ThetaBelowRoot)))) = true := by
  have h : ((childHH (childHH (childLH (childLL e24ThetaBelowRoot))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 (childHH (childHH (childLH (childLL e24ThetaBelowRoot)))) h

theorem e24KC2ThetaBelowLeaf02 :
    adaptiveCoverCheck 16 (childHL (childLL e24ThetaBelowRoot)) = true := by
  have h : physicallyIrrelevant (childHL (childLL e24ThetaBelowRoot)) = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_physicallyIrrelevant 16 (childHL (childLL e24ThetaBelowRoot)) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf030 :
    adaptiveCoverCheck 15 (childLL (childHH (childLL e24ThetaBelowRoot))) = true := by
  have h : ((childLL (childHH (childLL e24ThetaBelowRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 (childLL (childHH (childLL e24ThetaBelowRoot))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf031 :
    adaptiveCoverCheck 15 (childLH (childHH (childLL e24ThetaBelowRoot))) = true := by
  have h : ((childLH (childHH (childLL e24ThetaBelowRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 (childLH (childHH (childLL e24ThetaBelowRoot))) h

theorem e24KC2ThetaBelowLeaf032 :
    adaptiveCoverCheck 15 (childHL (childHH (childLL e24ThetaBelowRoot))) = true := by
  have h : physicallyIrrelevant (childHL (childHH (childLL e24ThetaBelowRoot))) = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_physicallyIrrelevant 15 (childHL (childHH (childLL e24ThetaBelowRoot))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf033 :
    adaptiveCoverCheck 15 (childHH (childHH (childLL e24ThetaBelowRoot))) = true := by
  have h : ((childHH (childHH (childLL e24ThetaBelowRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 (childHH (childHH (childLL e24ThetaBelowRoot))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf100000 :
    adaptiveCoverCheck 12 (childLL (childLL (childLL (childLL (childLL (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childLL (childLL (childLL (childLL (childLL (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childLL (childLL (childLL (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf100001 :
    adaptiveCoverCheck 12 (childLH (childLL (childLL (childLL (childLL (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childLH (childLL (childLL (childLL (childLL (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childLL (childLL (childLL (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf100002 :
    adaptiveCoverCheck 12 (childHL (childLL (childLL (childLL (childLL (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childHL (childLL (childLL (childLL (childLL (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL (childLL (childLL (childLL (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf100003 :
    adaptiveCoverCheck 12 (childHH (childLL (childLL (childLL (childLL (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childHH (childLL (childLL (childLL (childLL (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL (childLL (childLL (childLL (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf100010 :
    adaptiveCoverCheck 12 (childLL (childLH (childLL (childLL (childLL (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childLL (childLH (childLL (childLL (childLL (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childLL (childLL (childLL (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf100011 :
    adaptiveCoverCheck 12 (childLH (childLH (childLL (childLL (childLL (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childLH (childLH (childLL (childLL (childLL (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childLL (childLL (childLL (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf100012 :
    adaptiveCoverCheck 12 (childHL (childLH (childLL (childLL (childLL (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childHL (childLH (childLL (childLL (childLL (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childLL (childLL (childLL (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf100013 :
    adaptiveCoverCheck 12 (childHH (childLH (childLL (childLL (childLL (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childHH (childLH (childLL (childLL (childLL (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childLL (childLL (childLL (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf100020 :
    adaptiveCoverCheck 12 (childLL (childHL (childLL (childLL (childLL (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childLL (childHL (childLL (childLL (childLL (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childHL (childLL (childLL (childLL (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf100021 :
    adaptiveCoverCheck 12 (childLH (childHL (childLL (childLL (childLL (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childLH (childHL (childLL (childLL (childLL (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childHL (childLL (childLL (childLL (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf100022 :
    adaptiveCoverCheck 12 (childHL (childHL (childLL (childLL (childLL (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childHL (childHL (childLL (childLL (childLL (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childHL (childLL (childLL (childLL (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf100023 :
    adaptiveCoverCheck 12 (childHH (childHL (childLL (childLL (childLL (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childHH (childHL (childLL (childLL (childLL (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childHL (childLL (childLL (childLL (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf100030 :
    adaptiveCoverCheck 12 (childLL (childHH (childLL (childLL (childLL (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childLL (childHH (childLL (childLL (childLL (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childHH (childLL (childLL (childLL (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf100031 :
    adaptiveCoverCheck 12 (childLH (childHH (childLL (childLL (childLL (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childLH (childHH (childLL (childLL (childLL (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childHH (childLL (childLL (childLL (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf100032 :
    adaptiveCoverCheck 12 (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childHL (childHH (childLL (childLL (childLL (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childHH (childLL (childLL (childLL (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf100033 :
    adaptiveCoverCheck 12 (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childHH (childHH (childLL (childLL (childLL (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childHH (childLL (childLL (childLL (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf100100 :
    adaptiveCoverCheck 12 (childLL (childLL (childLH (childLL (childLL (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childLL (childLL (childLH (childLL (childLL (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childLH (childLL (childLL (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf100101 :
    adaptiveCoverCheck 12 (childLH (childLL (childLH (childLL (childLL (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childLH (childLL (childLH (childLL (childLL (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childLH (childLL (childLL (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf100102 :
    adaptiveCoverCheck 12 (childHL (childLL (childLH (childLL (childLL (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childHL (childLL (childLH (childLL (childLL (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL (childLH (childLL (childLL (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf100103 :
    adaptiveCoverCheck 12 (childHH (childLL (childLH (childLL (childLL (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childHH (childLL (childLH (childLL (childLL (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL (childLH (childLL (childLL (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf100110 :
    adaptiveCoverCheck 12 (childLL (childLH (childLH (childLL (childLL (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childLL (childLH (childLH (childLL (childLL (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childLH (childLL (childLL (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf100111 :
    adaptiveCoverCheck 12 (childLH (childLH (childLH (childLL (childLL (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childLH (childLH (childLH (childLL (childLL (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childLH (childLL (childLL (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf100112 :
    adaptiveCoverCheck 12 (childHL (childLH (childLH (childLL (childLL (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childHL (childLH (childLH (childLL (childLL (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childLH (childLL (childLL (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1001130 :
    adaptiveCoverCheck 11 (childLL (childHH (childLH (childLH (childLL (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLL (childHH (childLH (childLH (childLL (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHH (childLH (childLH (childLL (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1001131 :
    adaptiveCoverCheck 11 (childLH (childHH (childLH (childLH (childLL (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLH (childHH (childLH (childLH (childLL (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHH (childLH (childLH (childLL (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1001132 :
    adaptiveCoverCheck 11 (childHL (childHH (childLH (childLH (childLL (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHL (childHH (childLH (childLH (childLL (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childLH (childLH (childLL (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1001133 :
    adaptiveCoverCheck 11 (childHH (childHH (childLH (childLH (childLL (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHH (childHH (childLH (childLH (childLL (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childLH (childLH (childLL (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf100120 :
    adaptiveCoverCheck 12 (childLL (childHL (childLH (childLL (childLL (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childLL (childHL (childLH (childLL (childLL (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childHL (childLH (childLL (childLL (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1001210 :
    adaptiveCoverCheck 11 (childLL (childLH (childHL (childLH (childLL (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLL (childLH (childHL (childLH (childLL (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLH (childHL (childLH (childLL (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1001211 :
    adaptiveCoverCheck 11 (childLH (childLH (childHL (childLH (childLL (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLH (childLH (childHL (childLH (childLL (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLH (childHL (childLH (childLL (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1001212 :
    adaptiveCoverCheck 11 (childHL (childLH (childHL (childLH (childLL (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHL (childLH (childHL (childLH (childLL (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childLH (childHL (childLH (childLL (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1001213 :
    adaptiveCoverCheck 11 (childHH (childLH (childHL (childLH (childLL (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHH (childLH (childHL (childLH (childLL (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childLH (childHL (childLH (childLL (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf100122 :
    adaptiveCoverCheck 12 (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childHL (childHL (childLH (childLL (childLL (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childHL (childLH (childLL (childLL (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf100123 :
    adaptiveCoverCheck 12 (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childHH (childHL (childLH (childLL (childLL (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childHL (childLH (childLL (childLL (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1001300 :
    adaptiveCoverCheck 11 (childLL (childLL (childHH (childLH (childLL (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLL (childLL (childHH (childLH (childLL (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLL (childHH (childLH (childLL (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1001301 :
    adaptiveCoverCheck 11 (childLH (childLL (childHH (childLH (childLL (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLH (childLL (childHH (childLH (childLL (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLL (childHH (childLH (childLL (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1001302 :
    adaptiveCoverCheck 11 (childHL (childLL (childHH (childLH (childLL (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHL (childLL (childHH (childLH (childLL (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childLL (childHH (childLH (childLL (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1001303 :
    adaptiveCoverCheck 11 (childHH (childLL (childHH (childLH (childLL (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHH (childLL (childHH (childLH (childLL (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childLL (childHH (childLH (childLL (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1001310 :
    adaptiveCoverCheck 11 (childLL (childLH (childHH (childLH (childLL (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLL (childLH (childHH (childLH (childLL (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLH (childHH (childLH (childLL (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1001311 :
    adaptiveCoverCheck 11 (childLH (childLH (childHH (childLH (childLL (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLH (childLH (childHH (childLH (childLL (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLH (childHH (childLH (childLL (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1001312 :
    adaptiveCoverCheck 11 (childHL (childLH (childHH (childLH (childLL (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHL (childLH (childHH (childLH (childLL (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childLH (childHH (childLH (childLL (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1001313 :
    adaptiveCoverCheck 11 (childHH (childLH (childHH (childLH (childLL (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHH (childLH (childHH (childLH (childLL (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childLH (childHH (childLH (childLL (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf100132 :
    adaptiveCoverCheck 12 (childHL (childHH (childLH (childLL (childLL (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childHL (childHH (childLH (childLL (childLL (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childHH (childLH (childLL (childLL (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf100133 :
    adaptiveCoverCheck 12 (childHH (childHH (childLH (childLL (childLL (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childHH (childHH (childLH (childLL (childLL (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childHH (childLH (childLL (childLL (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf10020 :
    adaptiveCoverCheck 13 (childLL (childHL (childLL (childLL (childLH e24ThetaBelowRoot))))) = true := by
  have h : ((childLL (childHL (childLL (childLL (childLH e24ThetaBelowRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL (childHL (childLL (childLL (childLH e24ThetaBelowRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf10021 :
    adaptiveCoverCheck 13 (childLH (childHL (childLL (childLL (childLH e24ThetaBelowRoot))))) = true := by
  have h : ((childLH (childHL (childLL (childLL (childLH e24ThetaBelowRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH (childHL (childLL (childLL (childLH e24ThetaBelowRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf10022 :
    adaptiveCoverCheck 13 (childHL (childHL (childLL (childLL (childLH e24ThetaBelowRoot))))) = true := by
  have h : ((childHL (childHL (childLL (childLL (childLH e24ThetaBelowRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childHL (childLL (childLL (childLH e24ThetaBelowRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf10023 :
    adaptiveCoverCheck 13 (childHH (childHL (childLL (childLL (childLH e24ThetaBelowRoot))))) = true := by
  have h : ((childHH (childHL (childLL (childLL (childLH e24ThetaBelowRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childHL (childLL (childLL (childLH e24ThetaBelowRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf10030 :
    adaptiveCoverCheck 13 (childLL (childHH (childLL (childLL (childLH e24ThetaBelowRoot))))) = true := by
  have h : ((childLL (childHH (childLL (childLL (childLH e24ThetaBelowRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL (childHH (childLL (childLL (childLH e24ThetaBelowRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf100310 :
    adaptiveCoverCheck 12 (childLL (childLH (childHH (childLL (childLL (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childLL (childLH (childHH (childLL (childLL (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childHH (childLL (childLL (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf100311 :
    adaptiveCoverCheck 12 (childLH (childLH (childHH (childLL (childLL (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childLH (childLH (childHH (childLL (childLL (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childHH (childLL (childLL (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf100312 :
    adaptiveCoverCheck 12 (childHL (childLH (childHH (childLL (childLL (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childHL (childLH (childHH (childLL (childLL (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childHH (childLL (childLL (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf100313 :
    adaptiveCoverCheck 12 (childHH (childLH (childHH (childLL (childLL (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childHH (childLH (childHH (childLL (childLL (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childHH (childLL (childLL (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf10032 :
    adaptiveCoverCheck 13 (childHL (childHH (childLL (childLL (childLH e24ThetaBelowRoot))))) = true := by
  have h : ((childHL (childHH (childLL (childLL (childLH e24ThetaBelowRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childHH (childLL (childLL (childLH e24ThetaBelowRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf10033 :
    adaptiveCoverCheck 13 (childHH (childHH (childLL (childLL (childLH e24ThetaBelowRoot))))) = true := by
  have h : ((childHH (childHH (childLL (childLL (childLH e24ThetaBelowRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childHH (childLL (childLL (childLH e24ThetaBelowRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf101000 :
    adaptiveCoverCheck 12 (childLL (childLL (childLL (childLH (childLL (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childLL (childLL (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childLL (childLH (childLL (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1010010 :
    adaptiveCoverCheck 11 (childLL (childLH (childLL (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLL (childLH (childLL (childLL (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLH (childLL (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1010011 :
    adaptiveCoverCheck 11 (childLH (childLH (childLL (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLH (childLH (childLL (childLL (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLH (childLL (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1010012 :
    adaptiveCoverCheck 11 (childHL (childLH (childLL (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHL (childLH (childLL (childLL (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childLH (childLL (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1010013 :
    adaptiveCoverCheck 11 (childHH (childLH (childLL (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHH (childLH (childLL (childLL (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childLH (childLL (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1010020 :
    adaptiveCoverCheck 11 (childLL (childHL (childLL (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLL (childHL (childLL (childLL (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHL (childLL (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1010021 :
    adaptiveCoverCheck 11 (childLH (childHL (childLL (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLH (childHL (childLL (childLL (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHL (childLL (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1010022 :
    adaptiveCoverCheck 11 (childHL (childHL (childLL (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHL (childHL (childLL (childLL (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childLL (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1010023 :
    adaptiveCoverCheck 11 (childHH (childHL (childLL (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHH (childHL (childLL (childLL (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childLL (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1010030 :
    adaptiveCoverCheck 11 (childLL (childHH (childLL (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLL (childHH (childLL (childLL (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHH (childLL (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1010031 :
    adaptiveCoverCheck 11 (childLH (childHH (childLL (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLH (childHH (childLL (childLL (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHH (childLL (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1010032 :
    adaptiveCoverCheck 11 (childHL (childHH (childLL (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHL (childHH (childLL (childLL (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childLL (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1010033 :
    adaptiveCoverCheck 11 (childHH (childHH (childLL (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHH (childHH (childLL (childLL (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childLL (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1010100 :
    adaptiveCoverCheck 11 (childLL (childLL (childLH (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLL (childLL (childLH (childLL (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLL (childLH (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1010101 :
    adaptiveCoverCheck 11 (childLH (childLL (childLH (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLH (childLL (childLH (childLL (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLL (childLH (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1010102 :
    adaptiveCoverCheck 11 (childHL (childLL (childLH (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHL (childLL (childLH (childLL (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childLL (childLH (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1010103 :
    adaptiveCoverCheck 11 (childHH (childLL (childLH (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHH (childLL (childLH (childLL (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childLL (childLH (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1010110 :
    adaptiveCoverCheck 11 (childLL (childLH (childLH (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLL (childLH (childLH (childLL (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLH (childLH (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1010111 :
    adaptiveCoverCheck 11 (childLH (childLH (childLH (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLH (childLH (childLH (childLL (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLH (childLH (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1010112 :
    adaptiveCoverCheck 11 (childHL (childLH (childLH (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHL (childLH (childLH (childLL (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childLH (childLH (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1010113 :
    adaptiveCoverCheck 11 (childHH (childLH (childLH (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHH (childLH (childLH (childLL (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childLH (childLH (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1010120 :
    adaptiveCoverCheck 11 (childLL (childHL (childLH (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLL (childHL (childLH (childLL (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHL (childLH (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1010121 :
    adaptiveCoverCheck 11 (childLH (childHL (childLH (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLH (childHL (childLH (childLL (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHL (childLH (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1010122 :
    adaptiveCoverCheck 11 (childHL (childHL (childLH (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHL (childHL (childLH (childLL (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childLH (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1010123 :
    adaptiveCoverCheck 11 (childHH (childHL (childLH (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHH (childHL (childLH (childLL (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childLH (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1010130 :
    adaptiveCoverCheck 11 (childLL (childHH (childLH (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLL (childHH (childLH (childLL (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHH (childLH (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1010131 :
    adaptiveCoverCheck 11 (childLH (childHH (childLH (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLH (childHH (childLH (childLL (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHH (childLH (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1010132 :
    adaptiveCoverCheck 11 (childHL (childHH (childLH (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHL (childHH (childLH (childLL (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childLH (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1010133 :
    adaptiveCoverCheck 11 (childHH (childHH (childLH (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHH (childHH (childLH (childLL (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childLH (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1010200 :
    adaptiveCoverCheck 11 (childLL (childLL (childHL (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLL (childLL (childHL (childLL (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLL (childHL (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1010201 :
    adaptiveCoverCheck 11 (childLH (childLL (childHL (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLH (childLL (childHL (childLL (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLL (childHL (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1010202 :
    adaptiveCoverCheck 11 (childHL (childLL (childHL (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHL (childLL (childHL (childLL (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childLL (childHL (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1010203 :
    adaptiveCoverCheck 11 (childHH (childLL (childHL (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHH (childLL (childHL (childLL (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childLL (childHL (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1010210 :
    adaptiveCoverCheck 11 (childLL (childLH (childHL (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLL (childLH (childHL (childLL (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLH (childHL (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1010211 :
    adaptiveCoverCheck 11 (childLH (childLH (childHL (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLH (childLH (childHL (childLL (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLH (childHL (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1010212 :
    adaptiveCoverCheck 11 (childHL (childLH (childHL (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHL (childLH (childHL (childLL (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childLH (childHL (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1010213 :
    adaptiveCoverCheck 11 (childHH (childLH (childHL (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHH (childLH (childHL (childLL (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childLH (childHL (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf101022 :
    adaptiveCoverCheck 12 (childHL (childHL (childLL (childLH (childLL (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childHL (childHL (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childHL (childLL (childLH (childLL (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf101023 :
    adaptiveCoverCheck 12 (childHH (childHL (childLL (childLH (childLL (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childHH (childHL (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childHL (childLL (childLH (childLL (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1010300 :
    adaptiveCoverCheck 11 (childLL (childLL (childHH (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLL (childLL (childHH (childLL (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLL (childHH (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1010301 :
    adaptiveCoverCheck 11 (childLH (childLL (childHH (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLH (childLL (childHH (childLL (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLL (childHH (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1010302 :
    adaptiveCoverCheck 11 (childHL (childLL (childHH (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHL (childLL (childHH (childLL (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childLL (childHH (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1010303 :
    adaptiveCoverCheck 11 (childHH (childLL (childHH (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHH (childLL (childHH (childLL (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childLL (childHH (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1010310 :
    adaptiveCoverCheck 11 (childLL (childLH (childHH (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLL (childLH (childHH (childLL (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLH (childHH (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1010311 :
    adaptiveCoverCheck 11 (childLH (childLH (childHH (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLH (childLH (childHH (childLL (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLH (childHH (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1010312 :
    adaptiveCoverCheck 11 (childHL (childLH (childHH (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHL (childLH (childHH (childLL (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childLH (childHH (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1010313 :
    adaptiveCoverCheck 11 (childHH (childLH (childHH (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHH (childLH (childHH (childLL (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childLH (childHH (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1010320 :
    adaptiveCoverCheck 11 (childLL (childHL (childHH (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLL (childHL (childHH (childLL (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHL (childHH (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1010321 :
    adaptiveCoverCheck 11 (childLH (childHL (childHH (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLH (childHL (childHH (childLL (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHL (childHH (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1010322 :
    adaptiveCoverCheck 11 (childHL (childHL (childHH (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHL (childHL (childHH (childLL (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childHH (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1010323 :
    adaptiveCoverCheck 11 (childHH (childHL (childHH (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHH (childHL (childHH (childLL (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childHH (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1010330 :
    adaptiveCoverCheck 11 (childLL (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLL (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1010331 :
    adaptiveCoverCheck 11 (childLH (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLH (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1010332 :
    adaptiveCoverCheck 11 (childHL (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHL (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1010333 :
    adaptiveCoverCheck 11 (childHH (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHH (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childHH (childLL (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1011000 :
    adaptiveCoverCheck 11 (childLL (childLL (childLL (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLL (childLL (childLL (childLH (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLL (childLL (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1011001 :
    adaptiveCoverCheck 11 (childLH (childLL (childLL (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLH (childLL (childLL (childLH (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLL (childLL (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1011002 :
    adaptiveCoverCheck 11 (childHL (childLL (childLL (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHL (childLL (childLL (childLH (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childLL (childLL (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1011003 :
    adaptiveCoverCheck 11 (childHH (childLL (childLL (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHH (childLL (childLL (childLH (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childLL (childLL (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf101101 :
    adaptiveCoverCheck 12 (childLH (childLL (childLH (childLH (childLL (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childLH (childLL (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childLH (childLH (childLL (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1011020 :
    adaptiveCoverCheck 11 (childLL (childHL (childLL (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLL (childHL (childLL (childLH (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHL (childLL (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1011021 :
    adaptiveCoverCheck 11 (childLH (childHL (childLL (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLH (childHL (childLL (childLH (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHL (childLL (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1011022 :
    adaptiveCoverCheck 11 (childHL (childHL (childLL (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHL (childHL (childLL (childLH (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childLL (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1011023 :
    adaptiveCoverCheck 11 (childHH (childHL (childLL (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHH (childHL (childLL (childLH (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childLL (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1011030 :
    adaptiveCoverCheck 11 (childLL (childHH (childLL (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLL (childHH (childLL (childLH (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHH (childLL (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1011031 :
    adaptiveCoverCheck 11 (childLH (childHH (childLL (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLH (childHH (childLL (childLH (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHH (childLL (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1011032 :
    adaptiveCoverCheck 11 (childHL (childHH (childLL (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHL (childHH (childLL (childLH (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childLL (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1011033 :
    adaptiveCoverCheck 11 (childHH (childHH (childLL (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHH (childHH (childLL (childLH (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childLL (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf101110 :
    adaptiveCoverCheck 12 (childLL (childLH (childLH (childLH (childLL (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childLL (childLH (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childLH (childLH (childLL (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf101111 :
    adaptiveCoverCheck 12 (childLH (childLH (childLH (childLH (childLL (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childLH (childLH (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childLH (childLH (childLL (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1011120 :
    adaptiveCoverCheck 11 (childLL (childHL (childLH (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLL (childHL (childLH (childLH (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHL (childLH (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1011121 :
    adaptiveCoverCheck 11 (childLH (childHL (childLH (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLH (childHL (childLH (childLH (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHL (childLH (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1011122 :
    adaptiveCoverCheck 11 (childHL (childHL (childLH (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHL (childHL (childLH (childLH (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childLH (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1011123 :
    adaptiveCoverCheck 11 (childHH (childHL (childLH (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHH (childHL (childLH (childLH (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childLH (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1011130 :
    adaptiveCoverCheck 11 (childLL (childHH (childLH (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLL (childHH (childLH (childLH (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHH (childLH (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1011131 :
    adaptiveCoverCheck 11 (childLH (childHH (childLH (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLH (childHH (childLH (childLH (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHH (childLH (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1011132 :
    adaptiveCoverCheck 11 (childHL (childHH (childLH (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHL (childHH (childLH (childLH (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childLH (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1011133 :
    adaptiveCoverCheck 11 (childHH (childHH (childLH (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHH (childHH (childLH (childLH (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childLH (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1011200 :
    adaptiveCoverCheck 11 (childLL (childLL (childHL (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLL (childLL (childHL (childLH (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLL (childHL (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1011201 :
    adaptiveCoverCheck 11 (childLH (childLL (childHL (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLH (childLL (childHL (childLH (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLL (childHL (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1011202 :
    adaptiveCoverCheck 11 (childHL (childLL (childHL (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHL (childLL (childHL (childLH (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childLL (childHL (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1011203 :
    adaptiveCoverCheck 11 (childHH (childLL (childHL (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHH (childLL (childHL (childLH (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childLL (childHL (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1011210 :
    adaptiveCoverCheck 11 (childLL (childLH (childHL (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLL (childLH (childHL (childLH (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLH (childHL (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1011211 :
    adaptiveCoverCheck 11 (childLH (childLH (childHL (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLH (childLH (childHL (childLH (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLH (childHL (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1011212 :
    adaptiveCoverCheck 11 (childHL (childLH (childHL (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHL (childLH (childHL (childLH (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childLH (childHL (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1011213 :
    adaptiveCoverCheck 11 (childHH (childLH (childHL (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHH (childLH (childHL (childLH (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childLH (childHL (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1011220 :
    adaptiveCoverCheck 11 (childLL (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLL (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1011221 :
    adaptiveCoverCheck 11 (childLH (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLH (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1011222 :
    adaptiveCoverCheck 11 (childHL (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHL (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1011223 :
    adaptiveCoverCheck 11 (childHH (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHH (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childHL (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1011230 :
    adaptiveCoverCheck 11 (childLL (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLL (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1011231 :
    adaptiveCoverCheck 11 (childLH (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLH (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1011232 :
    adaptiveCoverCheck 11 (childHL (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHL (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1011233 :
    adaptiveCoverCheck 11 (childHH (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHH (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childHL (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1011300 :
    adaptiveCoverCheck 11 (childLL (childLL (childHH (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLL (childLL (childHH (childLH (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLL (childHH (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1011301 :
    adaptiveCoverCheck 11 (childLH (childLL (childHH (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLH (childLL (childHH (childLH (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLL (childHH (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1011302 :
    adaptiveCoverCheck 11 (childHL (childLL (childHH (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHL (childLL (childHH (childLH (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childLL (childHH (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf10113030 :
    adaptiveCoverCheck 10 (childLL (childHH (childLL (childHH (childLH (childLH (childLL (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLL (childHH (childLL (childHH (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHH (childLL (childHH (childLH (childLH (childLL (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf10113031 :
    adaptiveCoverCheck 10 (childLH (childHH (childLL (childHH (childLH (childLH (childLL (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLH (childHH (childLL (childHH (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHH (childLL (childHH (childLH (childLH (childLL (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf10113032 :
    adaptiveCoverCheck 10 (childHL (childHH (childLL (childHH (childLH (childLH (childLL (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHL (childHH (childLL (childHH (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childLL (childHH (childLH (childLH (childLL (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf10113033 :
    adaptiveCoverCheck 10 (childHH (childHH (childLL (childHH (childLH (childLH (childLL (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHH (childHH (childLL (childHH (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childLL (childHH (childLH (childLH (childLL (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1011310 :
    adaptiveCoverCheck 11 (childLL (childLH (childHH (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLL (childLH (childHH (childLH (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLH (childHH (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf10113110 :
    adaptiveCoverCheck 10 (childLL (childLH (childLH (childHH (childLH (childLH (childLL (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLL (childLH (childLH (childHH (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childLH (childHH (childLH (childLH (childLL (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf10113111 :
    adaptiveCoverCheck 10 (childLH (childLH (childLH (childHH (childLH (childLH (childLL (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLH (childLH (childLH (childHH (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childLH (childHH (childLH (childLH (childLL (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf10113112 :
    adaptiveCoverCheck 10 (childHL (childLH (childLH (childHH (childLH (childLH (childLL (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHL (childLH (childLH (childHH (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childLH (childHH (childLH (childLH (childLL (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf10113113 :
    adaptiveCoverCheck 10 (childHH (childLH (childLH (childHH (childLH (childLH (childLL (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHH (childLH (childLH (childHH (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childLH (childHH (childLH (childLH (childLL (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf10113120 :
    adaptiveCoverCheck 10 (childLL (childHL (childLH (childHH (childLH (childLH (childLL (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLL (childHL (childLH (childHH (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHL (childLH (childHH (childLH (childLH (childLL (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf10113121 :
    adaptiveCoverCheck 10 (childLH (childHL (childLH (childHH (childLH (childLH (childLL (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLH (childHL (childLH (childHH (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHL (childLH (childHH (childLH (childLH (childLL (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf10113122 :
    adaptiveCoverCheck 10 (childHL (childHL (childLH (childHH (childLH (childLH (childLL (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHL (childHL (childLH (childHH (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childLH (childHH (childLH (childLH (childLL (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf10113123 :
    adaptiveCoverCheck 10 (childHH (childHL (childLH (childHH (childLH (childLH (childLL (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHH (childHL (childLH (childHH (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childLH (childHH (childLH (childLH (childLL (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf10113130 :
    adaptiveCoverCheck 10 (childLL (childHH (childLH (childHH (childLH (childLH (childLL (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLL (childHH (childLH (childHH (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHH (childLH (childHH (childLH (childLH (childLL (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf10113131 :
    adaptiveCoverCheck 10 (childLH (childHH (childLH (childHH (childLH (childLH (childLL (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLH (childHH (childLH (childHH (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHH (childLH (childHH (childLH (childLH (childLL (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf10113132 :
    adaptiveCoverCheck 10 (childHL (childHH (childLH (childHH (childLH (childLH (childLL (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHL (childHH (childLH (childHH (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childLH (childHH (childLH (childLH (childLL (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf10113133 :
    adaptiveCoverCheck 10 (childHH (childHH (childLH (childHH (childLH (childLH (childLL (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHH (childHH (childLH (childHH (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childLH (childHH (childLH (childLH (childLL (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1011320 :
    adaptiveCoverCheck 11 (childLL (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLL (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1011321 :
    adaptiveCoverCheck 11 (childLH (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLH (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1011322 :
    adaptiveCoverCheck 11 (childHL (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHL (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1011323 :
    adaptiveCoverCheck 11 (childHH (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHH (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childHH (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1011330 :
    adaptiveCoverCheck 11 (childLL (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLL (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1011331 :
    adaptiveCoverCheck 11 (childLH (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLH (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1011332 :
    adaptiveCoverCheck 11 (childHL (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHL (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1011333 :
    adaptiveCoverCheck 11 (childHH (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHH (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childHH (childLH (childLH (childLL (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf101200 :
    adaptiveCoverCheck 12 (childLL (childLL (childHL (childLH (childLL (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childLL (childLL (childHL (childLH (childLL (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childHL (childLH (childLL (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf101201 :
    adaptiveCoverCheck 12 (childLH (childLL (childHL (childLH (childLL (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childLH (childLL (childHL (childLH (childLL (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childHL (childLH (childLL (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf101202 :
    adaptiveCoverCheck 12 (childHL (childLL (childHL (childLH (childLL (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childHL (childLL (childHL (childLH (childLL (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL (childHL (childLH (childLL (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf101203 :
    adaptiveCoverCheck 12 (childHH (childLL (childHL (childLH (childLL (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childHH (childLL (childHL (childLH (childLL (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL (childHL (childLH (childLL (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf101210 :
    adaptiveCoverCheck 12 (childLL (childLH (childHL (childLH (childLL (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childLL (childLH (childHL (childLH (childLL (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childHL (childLH (childLL (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf101211 :
    adaptiveCoverCheck 12 (childLH (childLH (childHL (childLH (childLL (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childLH (childLH (childHL (childLH (childLL (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childHL (childLH (childLL (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf101212 :
    adaptiveCoverCheck 12 (childHL (childLH (childHL (childLH (childLL (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childHL (childLH (childHL (childLH (childLL (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childHL (childLH (childLL (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf101213 :
    adaptiveCoverCheck 12 (childHH (childLH (childHL (childLH (childLL (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childHH (childLH (childHL (childLH (childLL (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childHL (childLH (childLL (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf10122 :
    adaptiveCoverCheck 13 (childHL (childHL (childLH (childLL (childLH e24ThetaBelowRoot))))) = true := by
  have h : ((childHL (childHL (childLH (childLL (childLH e24ThetaBelowRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childHL (childLH (childLL (childLH e24ThetaBelowRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf10123 :
    adaptiveCoverCheck 13 (childHH (childHL (childLH (childLL (childLH e24ThetaBelowRoot))))) = true := by
  have h : ((childHH (childHL (childLH (childLL (childLH e24ThetaBelowRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childHL (childLH (childLL (childLH e24ThetaBelowRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf101300 :
    adaptiveCoverCheck 12 (childLL (childLL (childHH (childLH (childLL (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childLL (childLL (childHH (childLH (childLL (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childHH (childLH (childLL (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf101301 :
    adaptiveCoverCheck 12 (childLH (childLL (childHH (childLH (childLL (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childLH (childLL (childHH (childLH (childLL (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childHH (childLH (childLL (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf101302 :
    adaptiveCoverCheck 12 (childHL (childLL (childHH (childLH (childLL (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childHL (childLL (childHH (childLH (childLL (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL (childHH (childLH (childLL (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf101303 :
    adaptiveCoverCheck 12 (childHH (childLL (childHH (childLH (childLL (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childHH (childLL (childHH (childLH (childLL (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL (childHH (childLH (childLL (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf101310 :
    adaptiveCoverCheck 12 (childLL (childLH (childHH (childLH (childLL (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childLL (childLH (childHH (childLH (childLL (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childHH (childLH (childLL (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf101311 :
    adaptiveCoverCheck 12 (childLH (childLH (childHH (childLH (childLL (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childLH (childLH (childHH (childLH (childLL (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childHH (childLH (childLL (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf101312 :
    adaptiveCoverCheck 12 (childHL (childLH (childHH (childLH (childLL (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childHL (childLH (childHH (childLH (childLL (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childHH (childLH (childLL (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf101313 :
    adaptiveCoverCheck 12 (childHH (childLH (childHH (childLH (childLL (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childHH (childLH (childHH (childLH (childLL (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childHH (childLH (childLL (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf10132 :
    adaptiveCoverCheck 13 (childHL (childHH (childLH (childLL (childLH e24ThetaBelowRoot))))) = true := by
  have h : ((childHL (childHH (childLH (childLL (childLH e24ThetaBelowRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childHH (childLH (childLL (childLH e24ThetaBelowRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf10133 :
    adaptiveCoverCheck 13 (childHH (childHH (childLH (childLL (childLH e24ThetaBelowRoot))))) = true := by
  have h : ((childHH (childHH (childLH (childLL (childLH e24ThetaBelowRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childHH (childLH (childLL (childLH e24ThetaBelowRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1020 :
    adaptiveCoverCheck 14 (childLL (childHL (childLL (childLH e24ThetaBelowRoot)))) = true := by
  have h : ((childLL (childHL (childLL (childLH e24ThetaBelowRoot))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 (childLL (childHL (childLL (childLH e24ThetaBelowRoot)))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1021 :
    adaptiveCoverCheck 14 (childLH (childHL (childLL (childLH e24ThetaBelowRoot)))) = true := by
  have h : ((childLH (childHL (childLL (childLH e24ThetaBelowRoot))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 (childLH (childHL (childLL (childLH e24ThetaBelowRoot)))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1022 :
    adaptiveCoverCheck 14 (childHL (childHL (childLL (childLH e24ThetaBelowRoot)))) = true := by
  have h : ((childHL (childHL (childLL (childLH e24ThetaBelowRoot))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 (childHL (childHL (childLL (childLH e24ThetaBelowRoot)))) h

end PartE
end GerverSofa
