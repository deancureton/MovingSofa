import GerverSofa.KernelOnly.PartE.E24KC2ProofHelpers

/-! E24KC5 checkpoint-aware kernel batch. -/
noncomputable section

namespace GerverSofa
namespace PartE

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110321030 :
    adaptiveCoverCheck 9 (childLL (childHH (childLL (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childLL (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childLL (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110321031 :
    adaptiveCoverCheck 9 (childLH (childHH (childLL (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childLL (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childLL (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110321032 :
    adaptiveCoverCheck 9 (childHL (childHH (childLL (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childLL (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childLL (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110321033 :
    adaptiveCoverCheck 9 (childHH (childHH (childLL (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childLL (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childLL (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011032110 :
    adaptiveCoverCheck 10 (childLL (childLH (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011032111 :
    adaptiveCoverCheck 10 (childLH (childLH (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110321120 :
    adaptiveCoverCheck 9 (childLL (childHL (childLH (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childLH (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childLH (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110321121 :
    adaptiveCoverCheck 9 (childLH (childHL (childLH (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childLH (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childLH (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110321122 :
    adaptiveCoverCheck 9 (childHL (childHL (childLH (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childLH (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childLH (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110321123 :
    adaptiveCoverCheck 9 (childHH (childHL (childLH (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childLH (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childLH (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110321130 :
    adaptiveCoverCheck 9 (childLL (childHH (childLH (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childLH (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childLH (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110321131 :
    adaptiveCoverCheck 9 (childLH (childHH (childLH (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childLH (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childLH (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110321132 :
    adaptiveCoverCheck 9 (childHL (childHH (childLH (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childLH (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childLH (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110321133 :
    adaptiveCoverCheck 9 (childHH (childHH (childLH (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childLH (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childLH (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110321200 :
    adaptiveCoverCheck 9 (childLL (childLL (childHL (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHL (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHL (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110321201 :
    adaptiveCoverCheck 9 (childLH (childLL (childHL (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHL (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHL (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110321202 :
    adaptiveCoverCheck 9 (childHL (childLL (childHL (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHL (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHL (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110321203 :
    adaptiveCoverCheck 9 (childHH (childLL (childHL (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHL (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHL (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110321210 :
    adaptiveCoverCheck 9 (childLL (childLH (childHL (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childHL (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHL (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110321211 :
    adaptiveCoverCheck 9 (childLH (childLH (childHL (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childHL (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHL (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110321212 :
    adaptiveCoverCheck 9 (childHL (childLH (childHL (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHL (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHL (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110321213 :
    adaptiveCoverCheck 9 (childHH (childLH (childHL (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHL (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHL (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110321220 :
    adaptiveCoverCheck 9 (childLL (childHL (childHL (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childHL (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childHL (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110321221 :
    adaptiveCoverCheck 9 (childLH (childHL (childHL (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childHL (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childHL (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110321222 :
    adaptiveCoverCheck 9 (childHL (childHL (childHL (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childHL (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childHL (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110321223 :
    adaptiveCoverCheck 9 (childHH (childHL (childHL (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childHL (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childHL (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110321230 :
    adaptiveCoverCheck 9 (childLL (childHH (childHL (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childHL (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childHL (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110321231 :
    adaptiveCoverCheck 9 (childLH (childHH (childHL (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childHL (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childHL (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110321232 :
    adaptiveCoverCheck 9 (childHL (childHH (childHL (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childHL (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childHL (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110321233 :
    adaptiveCoverCheck 9 (childHH (childHH (childHL (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childHL (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childHL (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110321300 :
    adaptiveCoverCheck 9 (childLL (childLL (childHH (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHH (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHH (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110321301 :
    adaptiveCoverCheck 9 (childLH (childLL (childHH (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHH (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHH (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110321302 :
    adaptiveCoverCheck 9 (childHL (childLL (childHH (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHH (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHH (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110321303 :
    adaptiveCoverCheck 9 (childHH (childLL (childHH (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHH (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHH (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110321310 :
    adaptiveCoverCheck 9 (childLL (childLH (childHH (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childHH (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHH (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110321311 :
    adaptiveCoverCheck 9 (childLH (childLH (childHH (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childHH (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHH (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110321312 :
    adaptiveCoverCheck 9 (childHL (childLH (childHH (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHH (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHH (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110321313 :
    adaptiveCoverCheck 9 (childHH (childLH (childHH (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHH (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHH (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110321320 :
    adaptiveCoverCheck 9 (childLL (childHL (childHH (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childHH (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childHH (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110321321 :
    adaptiveCoverCheck 9 (childLH (childHL (childHH (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childHH (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childHH (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110321322 :
    adaptiveCoverCheck 9 (childHL (childHL (childHH (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childHH (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childHH (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110321323 :
    adaptiveCoverCheck 9 (childHH (childHL (childHH (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childHH (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childHH (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110321330 :
    adaptiveCoverCheck 9 (childLL (childHH (childHH (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childHH (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childHH (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110321331 :
    adaptiveCoverCheck 9 (childLH (childHH (childHH (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childHH (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childHH (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110321332 :
    adaptiveCoverCheck 9 (childHL (childHH (childHH (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childHH (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childHH (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110321333 :
    adaptiveCoverCheck 9 (childHH (childHH (childHH (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childHH (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childHH (childLH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011032200 :
    adaptiveCoverCheck 10 (childLL (childLL (childHL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childHL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childHL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011032201 :
    adaptiveCoverCheck 10 (childLH (childLL (childHL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childHL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childHL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011032202 :
    adaptiveCoverCheck 10 (childHL (childLL (childHL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLL (childHL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childHL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011032203 :
    adaptiveCoverCheck 10 (childHH (childLL (childHL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLL (childHL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childHL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011032210 :
    adaptiveCoverCheck 10 (childLL (childLH (childHL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childHL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childHL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011032211 :
    adaptiveCoverCheck 10 (childLH (childLH (childHL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childHL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childHL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011032212 :
    adaptiveCoverCheck 10 (childHL (childLH (childHL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLH (childHL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childHL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011032213 :
    adaptiveCoverCheck 10 (childHH (childLH (childHL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLH (childHL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childHL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01103222 :
    adaptiveCoverCheck 11 (childHL (childHL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01103223 :
    adaptiveCoverCheck 11 (childHH (childHL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011032300 :
    adaptiveCoverCheck 10 (childLL (childLL (childHH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childHH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childHH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011032301 :
    adaptiveCoverCheck 10 (childLH (childLL (childHH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childHH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childHH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011032302 :
    adaptiveCoverCheck 10 (childHL (childLL (childHH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLL (childHH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childHH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011032303 :
    adaptiveCoverCheck 10 (childHH (childLL (childHH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLL (childHH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childHH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011032310 :
    adaptiveCoverCheck 10 (childLL (childLH (childHH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childHH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childHH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011032311 :
    adaptiveCoverCheck 10 (childLH (childLH (childHH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childHH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childHH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011032312 :
    adaptiveCoverCheck 10 (childHL (childLH (childHH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLH (childHH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childHH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011032313 :
    adaptiveCoverCheck 10 (childHH (childLH (childHH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLH (childHH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childHH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01103232 :
    adaptiveCoverCheck 11 (childHL (childHH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01103233 :
    adaptiveCoverCheck 11 (childHH (childHH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childHL (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011033000 :
    adaptiveCoverCheck 10 (childLL (childLL (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011033001 :
    adaptiveCoverCheck 10 (childLH (childLL (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110330020 :
    adaptiveCoverCheck 9 (childLL (childHL (childLL (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childLL (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childLL (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110330021 :
    adaptiveCoverCheck 9 (childLH (childHL (childLL (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childLL (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childLL (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110330022 :
    adaptiveCoverCheck 9 (childHL (childHL (childLL (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childLL (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childLL (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110330023 :
    adaptiveCoverCheck 9 (childHH (childHL (childLL (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childLL (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childLL (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110330030 :
    adaptiveCoverCheck 9 (childLL (childHH (childLL (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childLL (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childLL (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110330031 :
    adaptiveCoverCheck 9 (childLH (childHH (childLL (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childLL (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childLL (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110330032 :
    adaptiveCoverCheck 9 (childHL (childHH (childLL (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childLL (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childLL (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110330033 :
    adaptiveCoverCheck 9 (childHH (childHH (childLL (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childLL (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childLL (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011033010 :
    adaptiveCoverCheck 10 (childLL (childLH (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011033011 :
    adaptiveCoverCheck 10 (childLH (childLH (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110330120 :
    adaptiveCoverCheck 9 (childLL (childHL (childLH (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childLH (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childLH (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110330121 :
    adaptiveCoverCheck 9 (childLH (childHL (childLH (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childLH (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childLH (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110330122 :
    adaptiveCoverCheck 9 (childHL (childHL (childLH (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childLH (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childLH (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110330123 :
    adaptiveCoverCheck 9 (childHH (childHL (childLH (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childLH (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childLH (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110330130 :
    adaptiveCoverCheck 9 (childLL (childHH (childLH (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childLH (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childLH (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110330131 :
    adaptiveCoverCheck 9 (childLH (childHH (childLH (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childLH (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childLH (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110330132 :
    adaptiveCoverCheck 9 (childHL (childHH (childLH (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childLH (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childLH (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110330133 :
    adaptiveCoverCheck 9 (childHH (childHH (childLH (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childLH (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childLH (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110330200 :
    adaptiveCoverCheck 9 (childLL (childLL (childHL (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHL (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHL (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110330201 :
    adaptiveCoverCheck 9 (childLH (childLL (childHL (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHL (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHL (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110330202 :
    adaptiveCoverCheck 9 (childHL (childLL (childHL (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHL (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHL (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110330203 :
    adaptiveCoverCheck 9 (childHH (childLL (childHL (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHL (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHL (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110330210 :
    adaptiveCoverCheck 9 (childLL (childLH (childHL (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childHL (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHL (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110330211 :
    adaptiveCoverCheck 9 (childLH (childLH (childHL (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childHL (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHL (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110330212 :
    adaptiveCoverCheck 9 (childHL (childLH (childHL (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHL (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHL (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110330213 :
    adaptiveCoverCheck 9 (childHH (childLH (childHL (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHL (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHL (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110330220 :
    adaptiveCoverCheck 9 (childLL (childHL (childHL (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childHL (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childHL (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110330221 :
    adaptiveCoverCheck 9 (childLH (childHL (childHL (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childHL (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childHL (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110330222 :
    adaptiveCoverCheck 9 (childHL (childHL (childHL (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childHL (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childHL (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110330223 :
    adaptiveCoverCheck 9 (childHH (childHL (childHL (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childHL (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childHL (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110330230 :
    adaptiveCoverCheck 9 (childLL (childHH (childHL (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childHL (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childHL (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110330231 :
    adaptiveCoverCheck 9 (childLH (childHH (childHL (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childHL (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childHL (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110330232 :
    adaptiveCoverCheck 9 (childHL (childHH (childHL (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childHL (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childHL (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110330233 :
    adaptiveCoverCheck 9 (childHH (childHH (childHL (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childHL (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childHL (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110330300 :
    adaptiveCoverCheck 9 (childLL (childLL (childHH (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHH (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHH (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110330301 :
    adaptiveCoverCheck 9 (childLH (childLL (childHH (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHH (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHH (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110330302 :
    adaptiveCoverCheck 9 (childHL (childLL (childHH (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHH (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHH (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110330303 :
    adaptiveCoverCheck 9 (childHH (childLL (childHH (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHH (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHH (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110330310 :
    adaptiveCoverCheck 9 (childLL (childLH (childHH (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childHH (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHH (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110330311 :
    adaptiveCoverCheck 9 (childLH (childLH (childHH (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childHH (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHH (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110330312 :
    adaptiveCoverCheck 9 (childHL (childLH (childHH (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHH (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHH (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110330313 :
    adaptiveCoverCheck 9 (childHH (childLH (childHH (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHH (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHH (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110330320 :
    adaptiveCoverCheck 9 (childLL (childHL (childHH (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childHH (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childHH (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110330321 :
    adaptiveCoverCheck 9 (childLH (childHL (childHH (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childHH (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childHH (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110330322 :
    adaptiveCoverCheck 9 (childHL (childHL (childHH (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childHH (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childHH (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110330323 :
    adaptiveCoverCheck 9 (childHH (childHL (childHH (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childHH (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childHH (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110330330 :
    adaptiveCoverCheck 9 (childLL (childHH (childHH (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childHH (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childHH (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110330331 :
    adaptiveCoverCheck 9 (childLH (childHH (childHH (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childHH (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childHH (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110330332 :
    adaptiveCoverCheck 9 (childHL (childHH (childHH (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childHH (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childHH (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110330333 :
    adaptiveCoverCheck 9 (childHH (childHH (childHH (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childHH (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childHH (childLL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011033100 :
    adaptiveCoverCheck 10 (childLL (childLL (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011033101 :
    adaptiveCoverCheck 10 (childLH (childLL (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110331020 :
    adaptiveCoverCheck 9 (childLL (childHL (childLL (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childLL (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childLL (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110331021 :
    adaptiveCoverCheck 9 (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110331022 :
    adaptiveCoverCheck 9 (childHL (childHL (childLL (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childLL (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childLL (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110331023 :
    adaptiveCoverCheck 9 (childHH (childHL (childLL (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childLL (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childLL (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110331030 :
    adaptiveCoverCheck 9 (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110331031 :
    adaptiveCoverCheck 9 (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110331032 :
    adaptiveCoverCheck 9 (childHL (childHH (childLL (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childLL (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childLL (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110331033 :
    adaptiveCoverCheck 9 (childHH (childHH (childLL (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childLL (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childLL (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011033110 :
    adaptiveCoverCheck 10 (childLL (childLH (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011033111 :
    adaptiveCoverCheck 10 (childLH (childLH (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110331120 :
    adaptiveCoverCheck 9 (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110331121 :
    adaptiveCoverCheck 9 (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110331122 :
    adaptiveCoverCheck 9 (childHL (childHL (childLH (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childLH (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childLH (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110331123 :
    adaptiveCoverCheck 9 (childHH (childHL (childLH (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childLH (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childLH (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110331130 :
    adaptiveCoverCheck 9 (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110331131 :
    adaptiveCoverCheck 9 (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110331132 :
    adaptiveCoverCheck 9 (childHL (childHH (childLH (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childLH (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childLH (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110331133 :
    adaptiveCoverCheck 9 (childHH (childHH (childLH (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childLH (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childLH (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110331200 :
    adaptiveCoverCheck 9 (childLL (childLL (childHL (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHL (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHL (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110331201 :
    adaptiveCoverCheck 9 (childLH (childLL (childHL (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHL (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHL (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110331202 :
    adaptiveCoverCheck 9 (childHL (childLL (childHL (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHL (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHL (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110331203 :
    adaptiveCoverCheck 9 (childHH (childLL (childHL (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHL (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHL (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110331210 :
    adaptiveCoverCheck 9 (childLL (childLH (childHL (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childHL (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHL (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110331211 :
    adaptiveCoverCheck 9 (childLH (childLH (childHL (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childHL (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHL (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110331212 :
    adaptiveCoverCheck 9 (childHL (childLH (childHL (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHL (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHL (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110331213 :
    adaptiveCoverCheck 9 (childHH (childLH (childHL (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHL (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHL (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110331220 :
    adaptiveCoverCheck 9 (childLL (childHL (childHL (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childHL (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childHL (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110331221 :
    adaptiveCoverCheck 9 (childLH (childHL (childHL (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childHL (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childHL (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110331222 :
    adaptiveCoverCheck 9 (childHL (childHL (childHL (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childHL (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childHL (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110331223 :
    adaptiveCoverCheck 9 (childHH (childHL (childHL (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childHL (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childHL (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110331230 :
    adaptiveCoverCheck 9 (childLL (childHH (childHL (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childHL (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childHL (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110331231 :
    adaptiveCoverCheck 9 (childLH (childHH (childHL (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childHL (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childHL (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110331232 :
    adaptiveCoverCheck 9 (childHL (childHH (childHL (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childHL (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childHL (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110331233 :
    adaptiveCoverCheck 9 (childHH (childHH (childHL (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childHL (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childHL (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110331300 :
    adaptiveCoverCheck 9 (childLL (childLL (childHH (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHH (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHH (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110331301 :
    adaptiveCoverCheck 9 (childLH (childLL (childHH (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHH (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHH (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110331302 :
    adaptiveCoverCheck 9 (childHL (childLL (childHH (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHH (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHH (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110331303 :
    adaptiveCoverCheck 9 (childHH (childLL (childHH (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHH (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHH (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110331310 :
    adaptiveCoverCheck 9 (childLL (childLH (childHH (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childHH (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHH (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110331311 :
    adaptiveCoverCheck 9 (childLH (childLH (childHH (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childHH (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHH (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110331312 :
    adaptiveCoverCheck 9 (childHL (childLH (childHH (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHH (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHH (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110331313 :
    adaptiveCoverCheck 9 (childHH (childLH (childHH (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHH (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHH (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110331320 :
    adaptiveCoverCheck 9 (childLL (childHL (childHH (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childHH (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childHH (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110331321 :
    adaptiveCoverCheck 9 (childLH (childHL (childHH (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childHH (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childHH (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110331322 :
    adaptiveCoverCheck 9 (childHL (childHL (childHH (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childHH (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childHH (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110331323 :
    adaptiveCoverCheck 9 (childHH (childHL (childHH (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childHH (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childHH (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110331330 :
    adaptiveCoverCheck 9 (childLL (childHH (childHH (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childHH (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childHH (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110331331 :
    adaptiveCoverCheck 9 (childLH (childHH (childHH (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childHH (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childHH (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110331332 :
    adaptiveCoverCheck 9 (childHL (childHH (childHH (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childHH (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childHH (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0110331333 :
    adaptiveCoverCheck 9 (childHH (childHH (childHH (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childHH (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childHH (childLH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011033200 :
    adaptiveCoverCheck 10 (childLL (childLL (childHL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childHL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childHL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011033201 :
    adaptiveCoverCheck 10 (childLH (childLL (childHL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childHL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childHL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011033202 :
    adaptiveCoverCheck 10 (childHL (childLL (childHL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLL (childHL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childHL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011033203 :
    adaptiveCoverCheck 10 (childHH (childLL (childHL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLL (childHL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childHL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011033210 :
    adaptiveCoverCheck 10 (childLL (childLH (childHL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childHL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childHL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011033211 :
    adaptiveCoverCheck 10 (childLH (childLH (childHL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childHL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childHL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011033212 :
    adaptiveCoverCheck 10 (childHL (childLH (childHL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLH (childHL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childHL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011033213 :
    adaptiveCoverCheck 10 (childHH (childLH (childHL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLH (childHL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childHL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01103322 :
    adaptiveCoverCheck 11 (childHL (childHL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01103323 :
    adaptiveCoverCheck 11 (childHH (childHL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011033300 :
    adaptiveCoverCheck 10 (childLL (childLL (childHH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childHH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childHH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011033301 :
    adaptiveCoverCheck 10 (childLH (childLL (childHH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childHH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childHH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011033302 :
    adaptiveCoverCheck 10 (childHL (childLL (childHH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLL (childHH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childHH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011033303 :
    adaptiveCoverCheck 10 (childHH (childLL (childHH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLL (childHH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childHH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011033310 :
    adaptiveCoverCheck 10 (childLL (childLH (childHH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childHH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childHH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011033311 :
    adaptiveCoverCheck 10 (childLH (childLH (childHH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childHH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childHH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011033312 :
    adaptiveCoverCheck 10 (childHL (childLH (childHH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLH (childHH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childHH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011033313 :
    adaptiveCoverCheck 10 (childHH (childLH (childHH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLH (childHH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childHH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01103332 :
    adaptiveCoverCheck 11 (childHL (childHH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01103333 :
    adaptiveCoverCheck 11 (childHH (childHH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childHH (childHH (childLL (childLH (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011100 :
    adaptiveCoverCheck 13 (childLL (childLL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))) = true := by
  have h : ((childLL (childLL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL (childLL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011101 :
    adaptiveCoverCheck 13 (childLH (childLL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))) = true := by
  have h : ((childLH (childLL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH (childLL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011102 :
    adaptiveCoverCheck 13 (childHL (childLL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))) = true := by
  have h : ((childHL (childLL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011103 :
    adaptiveCoverCheck 13 (childHH (childLL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))) = true := by
  have h : ((childHH (childLL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011110 :
    adaptiveCoverCheck 13 (childLL (childLH (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))) = true := by
  have h : ((childLL (childLH (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL (childLH (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011111 :
    adaptiveCoverCheck 13 (childLH (childLH (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))) = true := by
  have h : ((childLH (childLH (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH (childLH (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011112 :
    adaptiveCoverCheck 13 (childHL (childLH (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))) = true := by
  have h : ((childHL (childLH (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLH (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011113 :
    adaptiveCoverCheck 13 (childHH (childLH (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))) = true := by
  have h : ((childHH (childLH (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLH (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111200 :
    adaptiveCoverCheck 12 (childLL (childLL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childLL (childLL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111201 :
    adaptiveCoverCheck 12 (childLH (childLL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childLH (childLL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01112020 :
    adaptiveCoverCheck 11 (childLL (childHL (childLL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childHL (childLL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHL (childLL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01112021 :
    adaptiveCoverCheck 11 (childLH (childHL (childLL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childHL (childLL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHL (childLL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01112022 :
    adaptiveCoverCheck 11 (childHL (childHL (childLL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHL (childLL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childLL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01112023 :
    adaptiveCoverCheck 11 (childHH (childHL (childLL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHL (childLL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childLL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01112030 :
    adaptiveCoverCheck 11 (childLL (childHH (childLL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childHH (childLL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHH (childLL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01112031 :
    adaptiveCoverCheck 11 (childLH (childHH (childLL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childHH (childLL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHH (childLL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01112032 :
    adaptiveCoverCheck 11 (childHL (childHH (childLL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHH (childLL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childLL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01112033 :
    adaptiveCoverCheck 11 (childHH (childHH (childLL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHH (childLL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childLL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111210 :
    adaptiveCoverCheck 12 (childLL (childLH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childLL (childLH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111211 :
    adaptiveCoverCheck 12 (childLH (childLH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childLH (childLH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01112120 :
    adaptiveCoverCheck 11 (childLL (childHL (childLH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childHL (childLH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHL (childLH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01112121 :
    adaptiveCoverCheck 11 (childLH (childHL (childLH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childHL (childLH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHL (childLH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01112122 :
    adaptiveCoverCheck 11 (childHL (childHL (childLH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHL (childLH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childLH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01112123 :
    adaptiveCoverCheck 11 (childHH (childHL (childLH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHL (childLH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childLH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01112130 :
    adaptiveCoverCheck 11 (childLL (childHH (childLH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childHH (childLH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHH (childLH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01112131 :
    adaptiveCoverCheck 11 (childLH (childHH (childLH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childHH (childLH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHH (childLH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01112132 :
    adaptiveCoverCheck 11 (childHL (childHH (childLH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHH (childLH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childLH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01112133 :
    adaptiveCoverCheck 11 (childHH (childHH (childLH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHH (childLH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childLH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011122000 :
    adaptiveCoverCheck 10 (childLL (childLL (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011122001 :
    adaptiveCoverCheck 10 (childLH (childLL (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111220020 :
    adaptiveCoverCheck 9 (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111220021 :
    adaptiveCoverCheck 9 (childLH (childHL (childLL (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childLL (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childLL (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111220022 :
    adaptiveCoverCheck 9 (childHL (childHL (childLL (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childLL (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childLL (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111220023 :
    adaptiveCoverCheck 9 (childHH (childHL (childLL (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childLL (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childLL (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111220030 :
    adaptiveCoverCheck 9 (childLL (childHH (childLL (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childLL (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childLL (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111220031 :
    adaptiveCoverCheck 9 (childLH (childHH (childLL (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childLL (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childLL (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111220032 :
    adaptiveCoverCheck 9 (childHL (childHH (childLL (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childLL (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childLL (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111220033 :
    adaptiveCoverCheck 9 (childHH (childHH (childLL (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childLL (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childLL (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011122010 :
    adaptiveCoverCheck 10 (childLL (childLH (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011122011 :
    adaptiveCoverCheck 10 (childLH (childLH (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111220120 :
    adaptiveCoverCheck 9 (childLL (childHL (childLH (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childLH (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childLH (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111220121 :
    adaptiveCoverCheck 9 (childLH (childHL (childLH (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childLH (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childLH (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111220122 :
    adaptiveCoverCheck 9 (childHL (childHL (childLH (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childLH (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childLH (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111220123 :
    adaptiveCoverCheck 9 (childHH (childHL (childLH (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childLH (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childLH (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111220130 :
    adaptiveCoverCheck 9 (childLL (childHH (childLH (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childLH (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childLH (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111220131 :
    adaptiveCoverCheck 9 (childLH (childHH (childLH (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childLH (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childLH (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111220132 :
    adaptiveCoverCheck 9 (childHL (childHH (childLH (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childLH (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childLH (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111220133 :
    adaptiveCoverCheck 9 (childHH (childHH (childLH (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childLH (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childLH (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111220200 :
    adaptiveCoverCheck 9 (childLL (childLL (childHL (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHL (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHL (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111220201 :
    adaptiveCoverCheck 9 (childLH (childLL (childHL (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHL (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHL (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111220202 :
    adaptiveCoverCheck 9 (childHL (childLL (childHL (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHL (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHL (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111220203 :
    adaptiveCoverCheck 9 (childHH (childLL (childHL (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHL (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHL (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111220210 :
    adaptiveCoverCheck 9 (childLL (childLH (childHL (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childHL (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHL (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111220211 :
    adaptiveCoverCheck 9 (childLH (childLH (childHL (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childHL (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHL (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111220212 :
    adaptiveCoverCheck 9 (childHL (childLH (childHL (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHL (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHL (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111220213 :
    adaptiveCoverCheck 9 (childHH (childLH (childHL (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHL (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHL (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111220220 :
    adaptiveCoverCheck 9 (childLL (childHL (childHL (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childHL (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childHL (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111220221 :
    adaptiveCoverCheck 9 (childLH (childHL (childHL (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childHL (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childHL (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111220222 :
    adaptiveCoverCheck 9 (childHL (childHL (childHL (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childHL (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childHL (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111220223 :
    adaptiveCoverCheck 9 (childHH (childHL (childHL (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childHL (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childHL (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111220230 :
    adaptiveCoverCheck 9 (childLL (childHH (childHL (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childHL (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childHL (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111220231 :
    adaptiveCoverCheck 9 (childLH (childHH (childHL (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childHL (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childHL (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111220232 :
    adaptiveCoverCheck 9 (childHL (childHH (childHL (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childHL (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childHL (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111220233 :
    adaptiveCoverCheck 9 (childHH (childHH (childHL (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childHL (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childHL (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111220300 :
    adaptiveCoverCheck 9 (childLL (childLL (childHH (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHH (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHH (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111220301 :
    adaptiveCoverCheck 9 (childLH (childLL (childHH (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHH (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHH (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111220302 :
    adaptiveCoverCheck 9 (childHL (childLL (childHH (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHH (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHH (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111220303 :
    adaptiveCoverCheck 9 (childHH (childLL (childHH (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHH (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHH (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111220310 :
    adaptiveCoverCheck 9 (childLL (childLH (childHH (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childHH (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHH (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111220311 :
    adaptiveCoverCheck 9 (childLH (childLH (childHH (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childHH (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHH (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111220312 :
    adaptiveCoverCheck 9 (childHL (childLH (childHH (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHH (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHH (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111220313 :
    adaptiveCoverCheck 9 (childHH (childLH (childHH (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHH (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHH (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111220320 :
    adaptiveCoverCheck 9 (childLL (childHL (childHH (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childHH (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childHH (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111220321 :
    adaptiveCoverCheck 9 (childLH (childHL (childHH (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childHH (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childHH (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111220322 :
    adaptiveCoverCheck 9 (childHL (childHL (childHH (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childHH (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childHH (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111220323 :
    adaptiveCoverCheck 9 (childHH (childHL (childHH (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childHH (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childHH (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111220330 :
    adaptiveCoverCheck 9 (childLL (childHH (childHH (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childHH (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childHH (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111220331 :
    adaptiveCoverCheck 9 (childLH (childHH (childHH (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childHH (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childHH (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111220332 :
    adaptiveCoverCheck 9 (childHL (childHH (childHH (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childHH (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childHH (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111220333 :
    adaptiveCoverCheck 9 (childHH (childHH (childHH (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childHH (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childHH (childLL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011122100 :
    adaptiveCoverCheck 10 (childLL (childLL (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011122101 :
    adaptiveCoverCheck 10 (childLH (childLL (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111221020 :
    adaptiveCoverCheck 9 (childLL (childHL (childLL (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childLL (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childLL (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111221021 :
    adaptiveCoverCheck 9 (childLH (childHL (childLL (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childLL (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childLL (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111221022 :
    adaptiveCoverCheck 9 (childHL (childHL (childLL (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childLL (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childLL (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111221023 :
    adaptiveCoverCheck 9 (childHH (childHL (childLL (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childLL (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childLL (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111221030 :
    adaptiveCoverCheck 9 (childLL (childHH (childLL (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childLL (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childLL (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111221031 :
    adaptiveCoverCheck 9 (childLH (childHH (childLL (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childLL (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childLL (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111221032 :
    adaptiveCoverCheck 9 (childHL (childHH (childLL (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childLL (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childLL (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111221033 :
    adaptiveCoverCheck 9 (childHH (childHH (childLL (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childLL (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childLL (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011122110 :
    adaptiveCoverCheck 10 (childLL (childLH (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011122111 :
    adaptiveCoverCheck 10 (childLH (childLH (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111221120 :
    adaptiveCoverCheck 9 (childLL (childHL (childLH (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childLH (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childLH (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111221121 :
    adaptiveCoverCheck 9 (childLH (childHL (childLH (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childLH (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childLH (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111221122 :
    adaptiveCoverCheck 9 (childHL (childHL (childLH (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childLH (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childLH (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111221123 :
    adaptiveCoverCheck 9 (childHH (childHL (childLH (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childLH (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childLH (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111221130 :
    adaptiveCoverCheck 9 (childLL (childHH (childLH (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childLH (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childLH (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111221131 :
    adaptiveCoverCheck 9 (childLH (childHH (childLH (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childLH (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childLH (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111221132 :
    adaptiveCoverCheck 9 (childHL (childHH (childLH (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childLH (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childLH (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111221133 :
    adaptiveCoverCheck 9 (childHH (childHH (childLH (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childLH (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childLH (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111221200 :
    adaptiveCoverCheck 9 (childLL (childLL (childHL (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHL (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHL (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111221201 :
    adaptiveCoverCheck 9 (childLH (childLL (childHL (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHL (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHL (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111221202 :
    adaptiveCoverCheck 9 (childHL (childLL (childHL (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHL (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHL (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111221203 :
    adaptiveCoverCheck 9 (childHH (childLL (childHL (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHL (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHL (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111221210 :
    adaptiveCoverCheck 9 (childLL (childLH (childHL (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childHL (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHL (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111221211 :
    adaptiveCoverCheck 9 (childLH (childLH (childHL (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childHL (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHL (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111221212 :
    adaptiveCoverCheck 9 (childHL (childLH (childHL (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHL (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHL (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111221213 :
    adaptiveCoverCheck 9 (childHH (childLH (childHL (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHL (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHL (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111221220 :
    adaptiveCoverCheck 9 (childLL (childHL (childHL (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childHL (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childHL (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111221221 :
    adaptiveCoverCheck 9 (childLH (childHL (childHL (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childHL (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childHL (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111221222 :
    adaptiveCoverCheck 9 (childHL (childHL (childHL (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childHL (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childHL (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111221223 :
    adaptiveCoverCheck 9 (childHH (childHL (childHL (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childHL (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childHL (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111221230 :
    adaptiveCoverCheck 9 (childLL (childHH (childHL (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childHL (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childHL (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111221231 :
    adaptiveCoverCheck 9 (childLH (childHH (childHL (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childHL (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childHL (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111221232 :
    adaptiveCoverCheck 9 (childHL (childHH (childHL (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childHL (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childHL (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111221233 :
    adaptiveCoverCheck 9 (childHH (childHH (childHL (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childHL (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childHL (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111221300 :
    adaptiveCoverCheck 9 (childLL (childLL (childHH (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHH (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHH (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111221301 :
    adaptiveCoverCheck 9 (childLH (childLL (childHH (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHH (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHH (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111221302 :
    adaptiveCoverCheck 9 (childHL (childLL (childHH (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHH (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHH (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111221303 :
    adaptiveCoverCheck 9 (childHH (childLL (childHH (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHH (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHH (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111221310 :
    adaptiveCoverCheck 9 (childLL (childLH (childHH (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childHH (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHH (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111221311 :
    adaptiveCoverCheck 9 (childLH (childLH (childHH (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childHH (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHH (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111221312 :
    adaptiveCoverCheck 9 (childHL (childLH (childHH (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHH (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHH (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111221313 :
    adaptiveCoverCheck 9 (childHH (childLH (childHH (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHH (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHH (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111221320 :
    adaptiveCoverCheck 9 (childLL (childHL (childHH (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childHH (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childHH (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111221321 :
    adaptiveCoverCheck 9 (childLH (childHL (childHH (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childHH (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childHH (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111221322 :
    adaptiveCoverCheck 9 (childHL (childHL (childHH (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childHH (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childHH (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111221323 :
    adaptiveCoverCheck 9 (childHH (childHL (childHH (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childHH (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childHH (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111221330 :
    adaptiveCoverCheck 9 (childLL (childHH (childHH (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childHH (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childHH (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111221331 :
    adaptiveCoverCheck 9 (childLH (childHH (childHH (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childHH (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childHH (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111221332 :
    adaptiveCoverCheck 9 (childHL (childHH (childHH (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childHH (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childHH (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111221333 :
    adaptiveCoverCheck 9 (childHH (childHH (childHH (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childHH (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childHH (childLH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011122200 :
    adaptiveCoverCheck 10 (childLL (childLL (childHL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childHL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childHL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011122201 :
    adaptiveCoverCheck 10 (childLH (childLL (childHL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childHL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childHL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011122202 :
    adaptiveCoverCheck 10 (childHL (childLL (childHL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLL (childHL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childHL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011122203 :
    adaptiveCoverCheck 10 (childHH (childLL (childHL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLL (childHL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childHL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011122210 :
    adaptiveCoverCheck 10 (childLL (childLH (childHL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childHL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childHL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011122211 :
    adaptiveCoverCheck 10 (childLH (childLH (childHL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childHL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childHL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011122212 :
    adaptiveCoverCheck 10 (childHL (childLH (childHL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLH (childHL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childHL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011122213 :
    adaptiveCoverCheck 10 (childHH (childLH (childHL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLH (childHL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childHL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01112222 :
    adaptiveCoverCheck 11 (childHL (childHL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01112223 :
    adaptiveCoverCheck 11 (childHH (childHL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011122300 :
    adaptiveCoverCheck 10 (childLL (childLL (childHH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childHH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childHH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011122301 :
    adaptiveCoverCheck 10 (childLH (childLL (childHH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childHH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childHH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011122302 :
    adaptiveCoverCheck 10 (childHL (childLL (childHH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLL (childHH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childHH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011122303 :
    adaptiveCoverCheck 10 (childHH (childLL (childHH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLL (childHH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childHH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011122310 :
    adaptiveCoverCheck 10 (childLL (childLH (childHH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childHH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childHH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011122311 :
    adaptiveCoverCheck 10 (childLH (childLH (childHH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childHH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childHH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011122312 :
    adaptiveCoverCheck 10 (childHL (childLH (childHH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLH (childHH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childHH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011122313 :
    adaptiveCoverCheck 10 (childHH (childLH (childHH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLH (childHH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childHH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01112232 :
    adaptiveCoverCheck 11 (childHL (childHH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01112233 :
    adaptiveCoverCheck 11 (childHH (childHH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childHL (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011123000 :
    adaptiveCoverCheck 10 (childLL (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011123001 :
    adaptiveCoverCheck 10 (childLH (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111230020 :
    adaptiveCoverCheck 9 (childLL (childHL (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111230021 :
    adaptiveCoverCheck 9 (childLH (childHL (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111230022 :
    adaptiveCoverCheck 9 (childHL (childHL (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111230023 :
    adaptiveCoverCheck 9 (childHH (childHL (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111230030 :
    adaptiveCoverCheck 9 (childLL (childHH (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111230031 :
    adaptiveCoverCheck 9 (childLH (childHH (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111230032 :
    adaptiveCoverCheck 9 (childHL (childHH (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111230033 :
    adaptiveCoverCheck 9 (childHH (childHH (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childLL (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011123010 :
    adaptiveCoverCheck 10 (childLL (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011123011 :
    adaptiveCoverCheck 10 (childLH (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111230120 :
    adaptiveCoverCheck 9 (childLL (childHL (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111230121 :
    adaptiveCoverCheck 9 (childLH (childHL (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111230122 :
    adaptiveCoverCheck 9 (childHL (childHL (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111230123 :
    adaptiveCoverCheck 9 (childHH (childHL (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111230130 :
    adaptiveCoverCheck 9 (childLL (childHH (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111230131 :
    adaptiveCoverCheck 9 (childLH (childHH (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111230132 :
    adaptiveCoverCheck 9 (childHL (childHH (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111230133 :
    adaptiveCoverCheck 9 (childHH (childHH (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childLH (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111230200 :
    adaptiveCoverCheck 9 (childLL (childLL (childHL (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHL (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHL (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111230201 :
    adaptiveCoverCheck 9 (childLH (childLL (childHL (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHL (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHL (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111230202 :
    adaptiveCoverCheck 9 (childHL (childLL (childHL (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHL (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHL (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111230203 :
    adaptiveCoverCheck 9 (childHH (childLL (childHL (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHL (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHL (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111230210 :
    adaptiveCoverCheck 9 (childLL (childLH (childHL (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childHL (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHL (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111230211 :
    adaptiveCoverCheck 9 (childLH (childLH (childHL (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childHL (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHL (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111230212 :
    adaptiveCoverCheck 9 (childHL (childLH (childHL (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHL (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHL (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111230213 :
    adaptiveCoverCheck 9 (childHH (childLH (childHL (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHL (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHL (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111230220 :
    adaptiveCoverCheck 9 (childLL (childHL (childHL (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childHL (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childHL (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111230221 :
    adaptiveCoverCheck 9 (childLH (childHL (childHL (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childHL (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childHL (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111230222 :
    adaptiveCoverCheck 9 (childHL (childHL (childHL (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childHL (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childHL (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111230223 :
    adaptiveCoverCheck 9 (childHH (childHL (childHL (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childHL (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childHL (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111230230 :
    adaptiveCoverCheck 9 (childLL (childHH (childHL (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childHL (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childHL (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111230231 :
    adaptiveCoverCheck 9 (childLH (childHH (childHL (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childHL (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childHL (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111230232 :
    adaptiveCoverCheck 9 (childHL (childHH (childHL (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childHL (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childHL (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111230233 :
    adaptiveCoverCheck 9 (childHH (childHH (childHL (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childHL (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childHL (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111230300 :
    adaptiveCoverCheck 9 (childLL (childLL (childHH (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHH (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHH (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111230301 :
    adaptiveCoverCheck 9 (childLH (childLL (childHH (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHH (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHH (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111230302 :
    adaptiveCoverCheck 9 (childHL (childLL (childHH (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHH (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHH (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111230303 :
    adaptiveCoverCheck 9 (childHH (childLL (childHH (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHH (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHH (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111230310 :
    adaptiveCoverCheck 9 (childLL (childLH (childHH (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childHH (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHH (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111230311 :
    adaptiveCoverCheck 9 (childLH (childLH (childHH (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childHH (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHH (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111230312 :
    adaptiveCoverCheck 9 (childHL (childLH (childHH (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHH (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHH (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111230313 :
    adaptiveCoverCheck 9 (childHH (childLH (childHH (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHH (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHH (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111230320 :
    adaptiveCoverCheck 9 (childLL (childHL (childHH (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childHH (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childHH (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111230321 :
    adaptiveCoverCheck 9 (childLH (childHL (childHH (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childHH (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childHH (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111230322 :
    adaptiveCoverCheck 9 (childHL (childHL (childHH (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childHH (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childHH (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111230323 :
    adaptiveCoverCheck 9 (childHH (childHL (childHH (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childHH (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childHH (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111230330 :
    adaptiveCoverCheck 9 (childLL (childHH (childHH (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childHH (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childHH (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111230331 :
    adaptiveCoverCheck 9 (childLH (childHH (childHH (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childHH (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childHH (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111230332 :
    adaptiveCoverCheck 9 (childHL (childHH (childHH (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childHH (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childHH (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111230333 :
    adaptiveCoverCheck 9 (childHH (childHH (childHH (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childHH (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childHH (childLL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011123100 :
    adaptiveCoverCheck 10 (childLL (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011123101 :
    adaptiveCoverCheck 10 (childLH (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111231020 :
    adaptiveCoverCheck 9 (childLL (childHL (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111231021 :
    adaptiveCoverCheck 9 (childLH (childHL (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111231022 :
    adaptiveCoverCheck 9 (childHL (childHL (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111231023 :
    adaptiveCoverCheck 9 (childHH (childHL (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111231030 :
    adaptiveCoverCheck 9 (childLL (childHH (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111231031 :
    adaptiveCoverCheck 9 (childLH (childHH (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111231032 :
    adaptiveCoverCheck 9 (childHL (childHH (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111231033 :
    adaptiveCoverCheck 9 (childHH (childHH (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childLL (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011123110 :
    adaptiveCoverCheck 10 (childLL (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011123111 :
    adaptiveCoverCheck 10 (childLH (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111231120 :
    adaptiveCoverCheck 9 (childLL (childHL (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111231121 :
    adaptiveCoverCheck 9 (childLH (childHL (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111231122 :
    adaptiveCoverCheck 9 (childHL (childHL (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111231123 :
    adaptiveCoverCheck 9 (childHH (childHL (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111231130 :
    adaptiveCoverCheck 9 (childLL (childHH (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111231131 :
    adaptiveCoverCheck 9 (childLH (childHH (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111231132 :
    adaptiveCoverCheck 9 (childHL (childHH (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111231133 :
    adaptiveCoverCheck 9 (childHH (childHH (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childLH (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111231200 :
    adaptiveCoverCheck 9 (childLL (childLL (childHL (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHL (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHL (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111231201 :
    adaptiveCoverCheck 9 (childLH (childLL (childHL (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHL (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHL (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111231202 :
    adaptiveCoverCheck 9 (childHL (childLL (childHL (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHL (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHL (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111231203 :
    adaptiveCoverCheck 9 (childHH (childLL (childHL (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHL (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHL (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111231210 :
    adaptiveCoverCheck 9 (childLL (childLH (childHL (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childHL (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHL (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111231211 :
    adaptiveCoverCheck 9 (childLH (childLH (childHL (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childHL (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHL (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111231212 :
    adaptiveCoverCheck 9 (childHL (childLH (childHL (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHL (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHL (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111231213 :
    adaptiveCoverCheck 9 (childHH (childLH (childHL (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHL (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHL (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111231220 :
    adaptiveCoverCheck 9 (childLL (childHL (childHL (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childHL (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childHL (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111231221 :
    adaptiveCoverCheck 9 (childLH (childHL (childHL (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childHL (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childHL (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111231222 :
    adaptiveCoverCheck 9 (childHL (childHL (childHL (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childHL (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childHL (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111231223 :
    adaptiveCoverCheck 9 (childHH (childHL (childHL (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childHL (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childHL (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111231230 :
    adaptiveCoverCheck 9 (childLL (childHH (childHL (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childHL (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childHL (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111231231 :
    adaptiveCoverCheck 9 (childLH (childHH (childHL (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childHL (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childHL (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111231232 :
    adaptiveCoverCheck 9 (childHL (childHH (childHL (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childHL (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childHL (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111231233 :
    adaptiveCoverCheck 9 (childHH (childHH (childHL (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childHL (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childHL (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111231300 :
    adaptiveCoverCheck 9 (childLL (childLL (childHH (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHH (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHH (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111231301 :
    adaptiveCoverCheck 9 (childLH (childLL (childHH (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHH (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHH (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111231302 :
    adaptiveCoverCheck 9 (childHL (childLL (childHH (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHH (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHH (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111231303 :
    adaptiveCoverCheck 9 (childHH (childLL (childHH (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHH (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHH (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111231310 :
    adaptiveCoverCheck 9 (childLL (childLH (childHH (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childHH (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHH (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111231311 :
    adaptiveCoverCheck 9 (childLH (childLH (childHH (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childHH (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHH (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111231312 :
    adaptiveCoverCheck 9 (childHL (childLH (childHH (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHH (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHH (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111231313 :
    adaptiveCoverCheck 9 (childHH (childLH (childHH (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHH (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHH (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111231320 :
    adaptiveCoverCheck 9 (childLL (childHL (childHH (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childHH (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childHH (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111231321 :
    adaptiveCoverCheck 9 (childLH (childHL (childHH (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childHH (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childHH (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111231322 :
    adaptiveCoverCheck 9 (childHL (childHL (childHH (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childHH (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childHH (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111231323 :
    adaptiveCoverCheck 9 (childHH (childHL (childHH (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childHH (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childHH (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111231330 :
    adaptiveCoverCheck 9 (childLL (childHH (childHH (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childHH (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childHH (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111231331 :
    adaptiveCoverCheck 9 (childLH (childHH (childHH (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childHH (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childHH (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111231332 :
    adaptiveCoverCheck 9 (childHL (childHH (childHH (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childHH (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childHH (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111231333 :
    adaptiveCoverCheck 9 (childHH (childHH (childHH (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childHH (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childHH (childLH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011123200 :
    adaptiveCoverCheck 10 (childLL (childLL (childHL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childHL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childHL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011123201 :
    adaptiveCoverCheck 10 (childLH (childLL (childHL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childHL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childHL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011123202 :
    adaptiveCoverCheck 10 (childHL (childLL (childHL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLL (childHL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childHL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011123203 :
    adaptiveCoverCheck 10 (childHH (childLL (childHL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLL (childHL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childHL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011123210 :
    adaptiveCoverCheck 10 (childLL (childLH (childHL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childHL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childHL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011123211 :
    adaptiveCoverCheck 10 (childLH (childLH (childHL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childHL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childHL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011123212 :
    adaptiveCoverCheck 10 (childHL (childLH (childHL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLH (childHL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childHL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011123213 :
    adaptiveCoverCheck 10 (childHH (childLH (childHL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLH (childHL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childHL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01112322 :
    adaptiveCoverCheck 11 (childHL (childHL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01112323 :
    adaptiveCoverCheck 11 (childHH (childHL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011123300 :
    adaptiveCoverCheck 10 (childLL (childLL (childHH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childHH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childHH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011123301 :
    adaptiveCoverCheck 10 (childLH (childLL (childHH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childHH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childHH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011123302 :
    adaptiveCoverCheck 10 (childHL (childLL (childHH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLL (childHH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childHH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011123303 :
    adaptiveCoverCheck 10 (childHH (childLL (childHH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLL (childHH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childHH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011123310 :
    adaptiveCoverCheck 10 (childLL (childLH (childHH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childHH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childHH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011123311 :
    adaptiveCoverCheck 10 (childLH (childLH (childHH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childHH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childHH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011123312 :
    adaptiveCoverCheck 10 (childHL (childLH (childHH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childLH (childHH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childHH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011123313 :
    adaptiveCoverCheck 10 (childHH (childLH (childHH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childLH (childHH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childHH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01112332 :
    adaptiveCoverCheck 11 (childHL (childHH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01112333 :
    adaptiveCoverCheck 11 (childHH (childHH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childHH (childHL (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111300 :
    adaptiveCoverCheck 12 (childLL (childLL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childLL (childLL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111301 :
    adaptiveCoverCheck 12 (childLH (childLL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childLH (childLL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01113020 :
    adaptiveCoverCheck 11 (childLL (childHL (childLL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childHL (childLL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHL (childLL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01113021 :
    adaptiveCoverCheck 11 (childLH (childHL (childLL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childHL (childLL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHL (childLL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01113022 :
    adaptiveCoverCheck 11 (childHL (childHL (childLL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHL (childLL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childLL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01113023 :
    adaptiveCoverCheck 11 (childHH (childHL (childLL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHL (childLL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childLL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01113030 :
    adaptiveCoverCheck 11 (childLL (childHH (childLL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childHH (childLL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHH (childLL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01113031 :
    adaptiveCoverCheck 11 (childLH (childHH (childLL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childHH (childLL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHH (childLL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01113032 :
    adaptiveCoverCheck 11 (childHL (childHH (childLL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHH (childLL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childLL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01113033 :
    adaptiveCoverCheck 11 (childHH (childHH (childLL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHH (childLL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childLL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111310 :
    adaptiveCoverCheck 12 (childLL (childLH (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childLL (childLH (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111311 :
    adaptiveCoverCheck 12 (childLH (childLH (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childLH (childLH (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01113120 :
    adaptiveCoverCheck 11 (childLL (childHL (childLH (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childHL (childLH (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHL (childLH (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01113121 :
    adaptiveCoverCheck 11 (childLH (childHL (childLH (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childHL (childLH (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHL (childLH (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01113122 :
    adaptiveCoverCheck 11 (childHL (childHL (childLH (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHL (childLH (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childLH (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01113123 :
    adaptiveCoverCheck 11 (childHH (childHL (childLH (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHL (childLH (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childLH (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01113130 :
    adaptiveCoverCheck 11 (childLL (childHH (childLH (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childHH (childLH (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHH (childLH (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01113131 :
    adaptiveCoverCheck 11 (childLH (childHH (childLH (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childHH (childLH (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHH (childLH (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01113132 :
    adaptiveCoverCheck 11 (childHL (childHH (childLH (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHH (childLH (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childLH (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf01113133 :
    adaptiveCoverCheck 11 (childHH (childHH (childLH (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHH (childLH (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childLH (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011132000 :
    adaptiveCoverCheck 10 (childLL (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011132001 :
    adaptiveCoverCheck 10 (childLH (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111320020 :
    adaptiveCoverCheck 9 (childLL (childHL (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111320021 :
    adaptiveCoverCheck 9 (childLH (childHL (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111320022 :
    adaptiveCoverCheck 9 (childHL (childHL (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111320023 :
    adaptiveCoverCheck 9 (childHH (childHL (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111320030 :
    adaptiveCoverCheck 9 (childLL (childHH (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111320031 :
    adaptiveCoverCheck 9 (childLH (childHH (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111320032 :
    adaptiveCoverCheck 9 (childHL (childHH (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111320033 :
    adaptiveCoverCheck 9 (childHH (childHH (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childLL (childLL (childHL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011132010 :
    adaptiveCoverCheck 10 (childLL (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf011132011 :
    adaptiveCoverCheck 10 (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111320120 :
    adaptiveCoverCheck 9 (childLL (childHL (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHL (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111320121 :
    adaptiveCoverCheck 9 (childLH (childHL (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHL (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111320122 :
    adaptiveCoverCheck 9 (childHL (childHL (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHL (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111320123 :
    adaptiveCoverCheck 9 (childHH (childHL (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHL (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111320130 :
    adaptiveCoverCheck 9 (childLL (childHH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childHH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111320131 :
    adaptiveCoverCheck 9 (childLH (childHH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childHH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111320132 :
    adaptiveCoverCheck 9 (childHL (childHH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childHH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111320133 :
    adaptiveCoverCheck 9 (childHH (childHH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childHH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childLH (childLL (childHL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111320200 :
    adaptiveCoverCheck 9 (childLL (childLL (childHL (childLL (childHL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHL (childLL (childHL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHL (childLL (childHL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111320201 :
    adaptiveCoverCheck 9 (childLH (childLL (childHL (childLL (childHL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHL (childLL (childHL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHL (childLL (childHL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111320202 :
    adaptiveCoverCheck 9 (childHL (childLL (childHL (childLL (childHL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHL (childLL (childHL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHL (childLL (childHL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111320203 :
    adaptiveCoverCheck 9 (childHH (childLL (childHL (childLL (childHL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHL (childLL (childHL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHL (childLL (childHL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111320210 :
    adaptiveCoverCheck 9 (childLL (childLH (childHL (childLL (childHL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childHL (childLL (childHL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHL (childLL (childHL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0111320211 :
    adaptiveCoverCheck 9 (childLH (childLH (childHL (childLL (childHL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childHL (childLL (childHL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHL (childLL (childHL (childHH (childLH (childLH (childLH (childLL e24ThetaAboveRoot)))))))))) h

end PartE
end GerverSofa
