import GerverSofa.KernelOnly.PartE.E24KC2ProofHelpers

/-! E24KC5 checkpoint-aware kernel batch. -/
noncomputable section

namespace GerverSofa
namespace PartE

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111030203 :
    adaptiveCoverCheck 9 (childHH (childLL (childHL (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHH (childLL (childHL (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHL (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111030210 :
    adaptiveCoverCheck 9 (childLL (childLH (childHL (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLL (childLH (childHL (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHL (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111030211 :
    adaptiveCoverCheck 9 (childLH (childLH (childHL (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLH (childLH (childHL (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHL (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111030212 :
    adaptiveCoverCheck 9 (childHL (childLH (childHL (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHL (childLH (childHL (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHL (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111030213 :
    adaptiveCoverCheck 9 (childHH (childLH (childHL (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHH (childLH (childHL (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHL (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111030220 :
    adaptiveCoverCheck 9 (childLL (childHL (childHL (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLL (childHL (childHL (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childHL (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111030221 :
    adaptiveCoverCheck 9 (childLH (childHL (childHL (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLH (childHL (childHL (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childHL (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111030222 :
    adaptiveCoverCheck 9 (childHL (childHL (childHL (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHL (childHL (childHL (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childHL (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111030230 :
    adaptiveCoverCheck 9 (childLL (childHH (childHL (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLL (childHH (childHL (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childHL (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111030231 :
    adaptiveCoverCheck 9 (childLH (childHH (childHL (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLH (childHH (childHL (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childHL (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111030300 :
    adaptiveCoverCheck 9 (childLL (childLL (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLL (childLL (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111030301 :
    adaptiveCoverCheck 9 (childLH (childLL (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLH (childLL (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111030302 :
    adaptiveCoverCheck 9 (childHL (childLL (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHL (childLL (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111030303 :
    adaptiveCoverCheck 9 (childHH (childLL (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHH (childLL (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111030310 :
    adaptiveCoverCheck 9 (childLL (childLH (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLL (childLH (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111030311 :
    adaptiveCoverCheck 9 (childLH (childLH (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLH (childLH (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHH (childLL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11103100 :
    adaptiveCoverCheck 10 (childLL (childLL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLL (childLL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11103101 :
    adaptiveCoverCheck 10 (childLH (childLL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLH (childLL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11103102 :
    adaptiveCoverCheck 10 (childHL (childLL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHL (childLL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11103103 :
    adaptiveCoverCheck 10 (childHH (childLL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHH (childLL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11103110 :
    adaptiveCoverCheck 10 (childLL (childLH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLL (childLH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11103111 :
    adaptiveCoverCheck 10 (childLH (childLH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLH (childLH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11103112 :
    adaptiveCoverCheck 10 (childHL (childLH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHL (childLH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11103113 :
    adaptiveCoverCheck 10 (childHH (childLH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHH (childLH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111031200 :
    adaptiveCoverCheck 9 (childLL (childLL (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLL (childLL (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111031201 :
    adaptiveCoverCheck 9 (childLH (childLL (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLH (childLL (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111031203 :
    adaptiveCoverCheck 9 (childHH (childLL (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHH (childLL (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111031210 :
    adaptiveCoverCheck 9 (childLL (childLH (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLL (childLH (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111031211 :
    adaptiveCoverCheck 9 (childLH (childLH (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLH (childLH (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111031212 :
    adaptiveCoverCheck 9 (childHL (childLH (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHL (childLH (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111031213 :
    adaptiveCoverCheck 9 (childHH (childLH (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHH (childLH (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHL (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111031300 :
    adaptiveCoverCheck 9 (childLL (childLL (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLL (childLL (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111031301 :
    adaptiveCoverCheck 9 (childLH (childLL (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLH (childLL (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111031302 :
    adaptiveCoverCheck 9 (childHL (childLL (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHL (childLL (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111031303 :
    adaptiveCoverCheck 9 (childHH (childLL (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHH (childLL (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111031310 :
    adaptiveCoverCheck 9 (childLL (childLH (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLL (childLH (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111031311 :
    adaptiveCoverCheck 9 (childLH (childLH (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLH (childLH (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111031312 :
    adaptiveCoverCheck 9 (childHL (childLH (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHL (childLH (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111031313 :
    adaptiveCoverCheck 9 (childHH (childLH (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHH (childLH (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHH (childLH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111032000 :
    adaptiveCoverCheck 9 (childLL (childLL (childLL (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLL (childLL (childLL (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childLL (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111032001 :
    adaptiveCoverCheck 9 (childLH (childLL (childLL (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLH (childLL (childLL (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childLL (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111032002 :
    adaptiveCoverCheck 9 (childHL (childLL (childLL (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHL (childLL (childLL (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childLL (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111032003 :
    adaptiveCoverCheck 9 (childHH (childLL (childLL (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHH (childLL (childLL (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childLL (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111032010 :
    adaptiveCoverCheck 9 (childLL (childLH (childLL (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLL (childLH (childLL (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childLL (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111032011 :
    adaptiveCoverCheck 9 (childLH (childLH (childLL (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLH (childLH (childLL (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childLL (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111032012 :
    adaptiveCoverCheck 9 (childHL (childLH (childLL (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHL (childLH (childLL (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childLL (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111032013 :
    adaptiveCoverCheck 9 (childHH (childLH (childLL (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHH (childLH (childLL (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childLL (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11103202 :
    adaptiveCoverCheck 10 (childHL (childLL (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHL (childLL (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11103203 :
    adaptiveCoverCheck 10 (childHH (childLL (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHH (childLL (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111032102 :
    adaptiveCoverCheck 9 (childHL (childLL (childLH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHL (childLL (childLH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childLH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111032103 :
    adaptiveCoverCheck 9 (childHH (childLL (childLH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHH (childLL (childLH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childLH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111032112 :
    adaptiveCoverCheck 9 (childHL (childLH (childLH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHL (childLH (childLH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childLH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111032113 :
    adaptiveCoverCheck 9 (childHH (childLH (childLH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHH (childLH (childLH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childLH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11103212 :
    adaptiveCoverCheck 10 (childHL (childLH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHL (childLH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11103213 :
    adaptiveCoverCheck 10 (childHH (childLH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHH (childLH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1110322 :
    adaptiveCoverCheck 11 (childHL (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHL (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1110323 :
    adaptiveCoverCheck 11 (childHH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111033002 :
    adaptiveCoverCheck 9 (childHL (childLL (childLL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHL (childLL (childLL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childLL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111033003 :
    adaptiveCoverCheck 9 (childHH (childLL (childLL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHH (childLL (childLL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childLL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111033012 :
    adaptiveCoverCheck 9 (childHL (childLH (childLL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHL (childLH (childLL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childLL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111033013 :
    adaptiveCoverCheck 9 (childHH (childLH (childLL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHH (childLH (childLL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childLL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11103302 :
    adaptiveCoverCheck 10 (childHL (childLL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHL (childLL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11103303 :
    adaptiveCoverCheck 10 (childHH (childLL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHH (childLL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111033102 :
    adaptiveCoverCheck 9 (childHL (childLL (childLH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHL (childLL (childLH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childLH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111033103 :
    adaptiveCoverCheck 9 (childHH (childLL (childLH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHH (childLL (childLH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childLH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111033112 :
    adaptiveCoverCheck 9 (childHL (childLH (childLH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHL (childLH (childLH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childLH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111033113 :
    adaptiveCoverCheck 9 (childHH (childLH (childLH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHH (childLH (childLH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childLH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11103312 :
    adaptiveCoverCheck 10 (childHL (childLH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHL (childLH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11103313 :
    adaptiveCoverCheck 10 (childHH (childLH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHH (childLH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1110332 :
    adaptiveCoverCheck 11 (childHL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1110333 :
    adaptiveCoverCheck 11 (childHH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childHH (childLL (childLH (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111100 :
    adaptiveCoverCheck 12 (childLL (childLL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childLL (childLL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111101 :
    adaptiveCoverCheck 12 (childLH (childLL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childLH (childLL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1111020 :
    adaptiveCoverCheck 11 (childLL (childHL (childLL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLL (childHL (childLL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHL (childLL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1111021 :
    adaptiveCoverCheck 11 (childLH (childHL (childLL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLH (childHL (childLL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHL (childLL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1111022 :
    adaptiveCoverCheck 11 (childHL (childHL (childLL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHL (childHL (childLL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childLL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1111023 :
    adaptiveCoverCheck 11 (childHH (childHL (childLL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHH (childHL (childLL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childLL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1111030 :
    adaptiveCoverCheck 11 (childLL (childHH (childLL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLL (childHH (childLL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHH (childLL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1111031 :
    adaptiveCoverCheck 11 (childLH (childHH (childLL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLH (childHH (childLL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHH (childLL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1111032 :
    adaptiveCoverCheck 11 (childHL (childHH (childLL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHL (childHH (childLL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childLL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1111033 :
    adaptiveCoverCheck 11 (childHH (childHH (childLL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHH (childHH (childLL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childLL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111110 :
    adaptiveCoverCheck 12 (childLL (childLH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childLL (childLH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111111 :
    adaptiveCoverCheck 12 (childLH (childLH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childLH (childLH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1111120 :
    adaptiveCoverCheck 11 (childLL (childHL (childLH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLL (childHL (childLH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHL (childLH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1111121 :
    adaptiveCoverCheck 11 (childLH (childHL (childLH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLH (childHL (childLH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHL (childLH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1111122 :
    adaptiveCoverCheck 11 (childHL (childHL (childLH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHL (childHL (childLH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childLH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1111123 :
    adaptiveCoverCheck 11 (childHH (childHL (childLH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHH (childHL (childLH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childLH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111113 :
    adaptiveCoverCheck 12 (childHH (childLH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childHH (childLH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11112000 :
    adaptiveCoverCheck 10 (childLL (childLL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLL (childLL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11112001 :
    adaptiveCoverCheck 10 (childLH (childLL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLH (childLL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11112002 :
    adaptiveCoverCheck 10 (childHL (childLL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHL (childLL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11112003 :
    adaptiveCoverCheck 10 (childHH (childLL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHH (childLL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11112010 :
    adaptiveCoverCheck 10 (childLL (childLH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLL (childLH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11112011 :
    adaptiveCoverCheck 10 (childLH (childLH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLH (childLH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11112012 :
    adaptiveCoverCheck 10 (childHL (childLH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHL (childLH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11112013 :
    adaptiveCoverCheck 10 (childHH (childLH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHH (childLH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111120200 :
    adaptiveCoverCheck 9 (childLL (childLL (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLL (childLL (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111120201 :
    adaptiveCoverCheck 9 (childLH (childLL (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLH (childLL (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111120202 :
    adaptiveCoverCheck 9 (childHL (childLL (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHL (childLL (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111120203 :
    adaptiveCoverCheck 9 (childHH (childLL (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHH (childLL (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111120210 :
    adaptiveCoverCheck 9 (childLL (childLH (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLL (childLH (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111120211 :
    adaptiveCoverCheck 9 (childLH (childLH (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLH (childLH (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111120212 :
    adaptiveCoverCheck 9 (childHL (childLH (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHL (childLH (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111120213 :
    adaptiveCoverCheck 9 (childHH (childLH (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHH (childLH (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHL (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111120300 :
    adaptiveCoverCheck 9 (childLL (childLL (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLL (childLL (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111120301 :
    adaptiveCoverCheck 9 (childLH (childLL (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLH (childLL (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111120302 :
    adaptiveCoverCheck 9 (childHL (childLL (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHL (childLL (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111120303 :
    adaptiveCoverCheck 9 (childHH (childLL (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHH (childLL (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111120310 :
    adaptiveCoverCheck 9 (childLL (childLH (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLL (childLH (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111120311 :
    adaptiveCoverCheck 9 (childLH (childLH (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLH (childLH (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111120312 :
    adaptiveCoverCheck 9 (childHL (childLH (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHL (childLH (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111120313 :
    adaptiveCoverCheck 9 (childHH (childLH (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHH (childLH (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHH (childLL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11112100 :
    adaptiveCoverCheck 10 (childLL (childLL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLL (childLL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11112101 :
    adaptiveCoverCheck 10 (childLH (childLL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLH (childLL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11112102 :
    adaptiveCoverCheck 10 (childHL (childLL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHL (childLL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11112103 :
    adaptiveCoverCheck 10 (childHH (childLL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHH (childLL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11112110 :
    adaptiveCoverCheck 10 (childLL (childLH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLL (childLH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11112111 :
    adaptiveCoverCheck 10 (childLH (childLH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLH (childLH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11112112 :
    adaptiveCoverCheck 10 (childHL (childLH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHL (childLH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11112113 :
    adaptiveCoverCheck 10 (childHH (childLH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHH (childLH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111121200 :
    adaptiveCoverCheck 9 (childLL (childLL (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLL (childLL (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111121201 :
    adaptiveCoverCheck 9 (childLH (childLL (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLH (childLL (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111121202 :
    adaptiveCoverCheck 9 (childHL (childLL (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHL (childLL (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111121203 :
    adaptiveCoverCheck 9 (childHH (childLL (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHH (childLL (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111121210 :
    adaptiveCoverCheck 9 (childLL (childLH (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLL (childLH (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111121211 :
    adaptiveCoverCheck 9 (childLH (childLH (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLH (childLH (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111121212 :
    adaptiveCoverCheck 9 (childHL (childLH (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHL (childLH (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111121213 :
    adaptiveCoverCheck 9 (childHH (childLH (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHH (childLH (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHL (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111121300 :
    adaptiveCoverCheck 9 (childLL (childLL (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLL (childLL (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111121301 :
    adaptiveCoverCheck 9 (childLH (childLL (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLH (childLL (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111121302 :
    adaptiveCoverCheck 9 (childHL (childLL (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHL (childLL (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111121303 :
    adaptiveCoverCheck 9 (childHH (childLL (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHH (childLL (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11112131 :
    adaptiveCoverCheck 10 (childLH (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLH (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111121320 :
    adaptiveCoverCheck 9 (childLL (childHL (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLL (childHL (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111121321 :
    adaptiveCoverCheck 9 (childLH (childHL (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLH (childHL (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111121330 :
    adaptiveCoverCheck 9 (childLL (childHH (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLL (childHH (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111121331 :
    adaptiveCoverCheck 9 (childLH (childHH (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLH (childHH (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childHH (childLH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111122002 :
    adaptiveCoverCheck 9 (childHL (childLL (childLL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHL (childLL (childLL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childLL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111122003 :
    adaptiveCoverCheck 9 (childHH (childLL (childLL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHH (childLL (childLL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childLL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111122012 :
    adaptiveCoverCheck 9 (childHL (childLH (childLL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHL (childLH (childLL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childLL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111122013 :
    adaptiveCoverCheck 9 (childHH (childLH (childLL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHH (childLH (childLL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childLL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11112202 :
    adaptiveCoverCheck 10 (childHL (childLL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHL (childLL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11112203 :
    adaptiveCoverCheck 10 (childHH (childLL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHH (childLL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111122102 :
    adaptiveCoverCheck 9 (childHL (childLL (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHL (childLL (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111122103 :
    adaptiveCoverCheck 9 (childHH (childLL (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHH (childLL (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111122112 :
    adaptiveCoverCheck 9 (childHL (childLH (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHL (childLH (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111122120 :
    adaptiveCoverCheck 9 (childLL (childHL (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLL (childHL (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111122121 :
    adaptiveCoverCheck 9 (childLH (childHL (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLH (childHL (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111122122 :
    adaptiveCoverCheck 9 (childHL (childHL (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHL (childHL (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111122123 :
    adaptiveCoverCheck 9 (childHH (childHL (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHH (childHL (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111122130 :
    adaptiveCoverCheck 9 (childLL (childHH (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLL (childHH (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111122131 :
    adaptiveCoverCheck 9 (childLH (childHH (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLH (childHH (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111122132 :
    adaptiveCoverCheck 9 (childHL (childHH (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHL (childHH (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111122133 :
    adaptiveCoverCheck 9 (childHH (childHH (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHH (childHH (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childLH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11112220 :
    adaptiveCoverCheck 10 (childLL (childHL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLL (childHL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11112221 :
    adaptiveCoverCheck 10 (childLH (childHL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLH (childHL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11112222 :
    adaptiveCoverCheck 10 (childHL (childHL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHL (childHL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11112223 :
    adaptiveCoverCheck 10 (childHH (childHL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHH (childHL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11112230 :
    adaptiveCoverCheck 10 (childLL (childHH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLL (childHH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11112231 :
    adaptiveCoverCheck 10 (childLH (childHH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLH (childHH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11112232 :
    adaptiveCoverCheck 10 (childHL (childHH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHL (childHH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11112233 :
    adaptiveCoverCheck 10 (childHH (childHH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHH (childHH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childHL (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111123020 :
    adaptiveCoverCheck 9 (childLL (childHL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLL (childHL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111123021 :
    adaptiveCoverCheck 9 (childLH (childHL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLH (childHL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111123022 :
    adaptiveCoverCheck 9 (childHL (childHL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHL (childHL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111123023 :
    adaptiveCoverCheck 9 (childHH (childHL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHH (childHL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111123030 :
    adaptiveCoverCheck 9 (childLL (childHH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLL (childHH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111123031 :
    adaptiveCoverCheck 9 (childLH (childHH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLH (childHH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111123032 :
    adaptiveCoverCheck 9 (childHL (childHH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHL (childHH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111123033 :
    adaptiveCoverCheck 9 (childHH (childHH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHH (childHH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childLL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111123120 :
    adaptiveCoverCheck 9 (childLL (childHL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLL (childHL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111123121 :
    adaptiveCoverCheck 9 (childLH (childHL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLH (childHL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111123122 :
    adaptiveCoverCheck 9 (childHL (childHL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHL (childHL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111123123 :
    adaptiveCoverCheck 9 (childHH (childHL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHH (childHL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111123130 :
    adaptiveCoverCheck 9 (childLL (childHH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLL (childHH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111123131 :
    adaptiveCoverCheck 9 (childLH (childHH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLH (childHH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111123132 :
    adaptiveCoverCheck 9 (childHL (childHH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHL (childHH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111123133 :
    adaptiveCoverCheck 9 (childHH (childHH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHH (childHH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childLH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11112320 :
    adaptiveCoverCheck 10 (childLL (childHL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLL (childHL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11112321 :
    adaptiveCoverCheck 10 (childLH (childHL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLH (childHL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11112322 :
    adaptiveCoverCheck 10 (childHL (childHL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHL (childHL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11112323 :
    adaptiveCoverCheck 10 (childHH (childHL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHH (childHL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11112330 :
    adaptiveCoverCheck 10 (childLL (childHH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLL (childHH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11112331 :
    adaptiveCoverCheck 10 (childLH (childHH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLH (childHH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11112332 :
    adaptiveCoverCheck 10 (childHL (childHH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHL (childHH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11112333 :
    adaptiveCoverCheck 10 (childHH (childHH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHH (childHH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childHH (childHL (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1111300 :
    adaptiveCoverCheck 11 (childLL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1111301 :
    adaptiveCoverCheck 11 (childLH (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLH (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11113020 :
    adaptiveCoverCheck 10 (childLL (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLL (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11113021 :
    adaptiveCoverCheck 10 (childLH (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLH (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111130220 :
    adaptiveCoverCheck 9 (childLL (childHL (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLL (childHL (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111130221 :
    adaptiveCoverCheck 9 (childLH (childHL (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLH (childHL (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111130230 :
    adaptiveCoverCheck 9 (childLL (childHH (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLL (childHH (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111130231 :
    adaptiveCoverCheck 9 (childLH (childHH (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLH (childHH (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childHL (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11113030 :
    adaptiveCoverCheck 10 (childLL (childHH (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLL (childHH (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHH (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11113031 :
    adaptiveCoverCheck 10 (childLH (childHH (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLH (childHH (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHH (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111130320 :
    adaptiveCoverCheck 9 (childLL (childHL (childHH (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLL (childHL (childHH (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childHH (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111130321 :
    adaptiveCoverCheck 9 (childLH (childHL (childHH (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLH (childHL (childHH (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childHH (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111130330 :
    adaptiveCoverCheck 9 (childLL (childHH (childHH (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLL (childHH (childHH (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childHH (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111130331 :
    adaptiveCoverCheck 9 (childLH (childHH (childHH (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLH (childHH (childHH (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childHH (childLL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1111310 :
    adaptiveCoverCheck 11 (childLL (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLL (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1111311 :
    adaptiveCoverCheck 11 (childLH (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLH (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11113120 :
    adaptiveCoverCheck 10 (childLL (childHL (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLL (childHL (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHL (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11113121 :
    adaptiveCoverCheck 10 (childLH (childHL (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLH (childHL (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHL (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111131220 :
    adaptiveCoverCheck 9 (childLL (childHL (childHL (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLL (childHL (childHL (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childHL (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111131221 :
    adaptiveCoverCheck 9 (childLH (childHL (childHL (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLH (childHL (childHL (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childHL (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111131230 :
    adaptiveCoverCheck 9 (childLL (childHH (childHL (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLL (childHH (childHL (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childHL (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111131231 :
    adaptiveCoverCheck 9 (childLH (childHH (childHL (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLH (childHH (childHL (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childHL (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11113130 :
    adaptiveCoverCheck 10 (childLL (childHH (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLL (childHH (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHH (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11113131 :
    adaptiveCoverCheck 10 (childLH (childHH (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLH (childHH (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHH (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111131320 :
    adaptiveCoverCheck 9 (childLL (childHL (childHH (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLL (childHL (childHH (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childHH (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111131321 :
    adaptiveCoverCheck 9 (childLH (childHL (childHH (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLH (childHL (childHH (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childHH (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111131330 :
    adaptiveCoverCheck 9 (childLL (childHH (childHH (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLL (childHH (childHH (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childHH (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111131331 :
    adaptiveCoverCheck 9 (childLH (childHH (childHH (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLH (childHH (childHH (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childHH (childLH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111132020 :
    adaptiveCoverCheck 9 (childLL (childHL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLL (childHL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111132021 :
    adaptiveCoverCheck 9 (childLH (childHL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLH (childHL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111132022 :
    adaptiveCoverCheck 9 (childHL (childHL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHL (childHL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111132023 :
    adaptiveCoverCheck 9 (childHH (childHL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHH (childHL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111132030 :
    adaptiveCoverCheck 9 (childLL (childHH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLL (childHH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111132031 :
    adaptiveCoverCheck 9 (childLH (childHH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLH (childHH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111132032 :
    adaptiveCoverCheck 9 (childHL (childHH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHL (childHH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111132033 :
    adaptiveCoverCheck 9 (childHH (childHH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHH (childHH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childLL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111132120 :
    adaptiveCoverCheck 9 (childLL (childHL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLL (childHL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111132121 :
    adaptiveCoverCheck 9 (childLH (childHL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLH (childHL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111132122 :
    adaptiveCoverCheck 9 (childHL (childHL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHL (childHL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111132123 :
    adaptiveCoverCheck 9 (childHH (childHL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHH (childHL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111132130 :
    adaptiveCoverCheck 9 (childLL (childHH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLL (childHH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111132131 :
    adaptiveCoverCheck 9 (childLH (childHH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLH (childHH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111132132 :
    adaptiveCoverCheck 9 (childHL (childHH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHL (childHH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111132133 :
    adaptiveCoverCheck 9 (childHH (childHH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHH (childHH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childLH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11113220 :
    adaptiveCoverCheck 10 (childLL (childHL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLL (childHL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11113221 :
    adaptiveCoverCheck 10 (childLH (childHL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLH (childHL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11113222 :
    adaptiveCoverCheck 10 (childHL (childHL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHL (childHL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11113223 :
    adaptiveCoverCheck 10 (childHH (childHL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHH (childHL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11113230 :
    adaptiveCoverCheck 10 (childLL (childHH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLL (childHH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11113231 :
    adaptiveCoverCheck 10 (childLH (childHH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLH (childHH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11113232 :
    adaptiveCoverCheck 10 (childHL (childHH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHL (childHH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11113233 :
    adaptiveCoverCheck 10 (childHH (childHH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHH (childHH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childHL (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111133020 :
    adaptiveCoverCheck 9 (childLL (childHL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLL (childHL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111133021 :
    adaptiveCoverCheck 9 (childLH (childHL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLH (childHL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111133022 :
    adaptiveCoverCheck 9 (childHL (childHL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHL (childHL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111133023 :
    adaptiveCoverCheck 9 (childHH (childHL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHH (childHL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111133030 :
    adaptiveCoverCheck 9 (childLL (childHH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLL (childHH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111133031 :
    adaptiveCoverCheck 9 (childLH (childHH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childLH (childHH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111133032 :
    adaptiveCoverCheck 9 (childHL (childHH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHL (childHH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111133033 :
    adaptiveCoverCheck 9 (childHH (childHH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHH (childHH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childLL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111133122 :
    adaptiveCoverCheck 9 (childHL (childHL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHL (childHL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111133123 :
    adaptiveCoverCheck 9 (childHH (childHL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHH (childHL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111133132 :
    adaptiveCoverCheck 9 (childHL (childHH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHL (childHH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111133133 :
    adaptiveCoverCheck 9 (childHH (childHH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) = true := by
  have h : ((childHH (childHH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childLH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11113320 :
    adaptiveCoverCheck 10 (childLL (childHL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLL (childHL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11113321 :
    adaptiveCoverCheck 10 (childLH (childHL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLH (childHL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11113322 :
    adaptiveCoverCheck 10 (childHL (childHL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHL (childHL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11113323 :
    adaptiveCoverCheck 10 (childHH (childHL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHH (childHL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11113330 :
    adaptiveCoverCheck 10 (childLL (childHH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLL (childHH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11113331 :
    adaptiveCoverCheck 10 (childLH (childHH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childLH (childHH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11113332 :
    adaptiveCoverCheck 10 (childHL (childHH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHL (childHH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11113333 :
    adaptiveCoverCheck 10 (childHH (childHH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) = true := by
  have h : ((childHH (childHH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childHH (childHH (childLH (childLH (childLH (childLH e24ThetaBelowRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111200 :
    adaptiveCoverCheck 12 (childLL (childLL (childHL (childLH (childLH (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childLL (childLL (childHL (childLH (childLH (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childHL (childLH (childLH (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111201 :
    adaptiveCoverCheck 12 (childLH (childLL (childHL (childLH (childLH (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childLH (childLL (childHL (childLH (childLH (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childHL (childLH (childLH (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111202 :
    adaptiveCoverCheck 12 (childHL (childLL (childHL (childLH (childLH (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childHL (childLL (childHL (childLH (childLH (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL (childHL (childLH (childLH (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111203 :
    adaptiveCoverCheck 12 (childHH (childLL (childHL (childLH (childLH (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childHH (childLL (childHL (childLH (childLH (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL (childHL (childLH (childLH (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1112100 :
    adaptiveCoverCheck 11 (childLL (childLL (childLH (childHL (childLH (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLL (childLL (childLH (childHL (childLH (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLL (childLH (childHL (childLH (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1112101 :
    adaptiveCoverCheck 11 (childLH (childLL (childLH (childHL (childLH (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLH (childLL (childLH (childHL (childLH (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLL (childLH (childHL (childLH (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1112102 :
    adaptiveCoverCheck 11 (childHL (childLL (childLH (childHL (childLH (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHL (childLL (childLH (childHL (childLH (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childLL (childLH (childHL (childLH (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1112103 :
    adaptiveCoverCheck 11 (childHH (childLL (childLH (childHL (childLH (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHH (childLL (childLH (childHL (childLH (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childLL (childLH (childHL (childLH (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1112110 :
    adaptiveCoverCheck 11 (childLL (childLH (childLH (childHL (childLH (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLL (childLH (childLH (childHL (childLH (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLH (childLH (childHL (childLH (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1112111 :
    adaptiveCoverCheck 11 (childLH (childLH (childLH (childHL (childLH (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLH (childLH (childLH (childHL (childLH (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLH (childLH (childHL (childLH (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1112112 :
    adaptiveCoverCheck 11 (childHL (childLH (childLH (childHL (childLH (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHL (childLH (childLH (childHL (childLH (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childLH (childLH (childHL (childLH (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1112113 :
    adaptiveCoverCheck 11 (childHH (childLH (childLH (childHL (childLH (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHH (childLH (childLH (childHL (childLH (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childLH (childLH (childHL (childLH (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111212 :
    adaptiveCoverCheck 12 (childHL (childLH (childHL (childLH (childLH (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childHL (childLH (childHL (childLH (childLH (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childHL (childLH (childLH (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111213 :
    adaptiveCoverCheck 12 (childHH (childLH (childHL (childLH (childLH (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childHH (childLH (childHL (childLH (childLH (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childHL (childLH (childLH (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11122 :
    adaptiveCoverCheck 13 (childHL (childHL (childLH (childLH (childLH e24ThetaBelowRoot))))) = true := by
  have h : ((childHL (childHL (childLH (childLH (childLH e24ThetaBelowRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childHL (childLH (childLH (childLH e24ThetaBelowRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11123 :
    adaptiveCoverCheck 13 (childHH (childHL (childLH (childLH (childLH e24ThetaBelowRoot))))) = true := by
  have h : ((childHH (childHL (childLH (childLH (childLH e24ThetaBelowRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childHL (childLH (childLH (childLH e24ThetaBelowRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1113000 :
    adaptiveCoverCheck 11 (childLL (childLL (childLL (childHH (childLH (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLL (childLL (childLL (childHH (childLH (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLL (childLL (childHH (childLH (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1113001 :
    adaptiveCoverCheck 11 (childLH (childLL (childLL (childHH (childLH (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLH (childLL (childLL (childHH (childLH (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLL (childLL (childHH (childLH (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1113002 :
    adaptiveCoverCheck 11 (childHL (childLL (childLL (childHH (childLH (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHL (childLL (childLL (childHH (childLH (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childLL (childLL (childHH (childLH (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1113003 :
    adaptiveCoverCheck 11 (childHH (childLL (childLL (childHH (childLH (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHH (childLL (childLL (childHH (childLH (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childLL (childLL (childHH (childLH (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1113010 :
    adaptiveCoverCheck 11 (childLL (childLH (childLL (childHH (childLH (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLL (childLH (childLL (childHH (childLH (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLH (childLL (childHH (childLH (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1113011 :
    adaptiveCoverCheck 11 (childLH (childLH (childLL (childHH (childLH (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLH (childLH (childLL (childHH (childLH (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLH (childLL (childHH (childLH (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1113012 :
    adaptiveCoverCheck 11 (childHL (childLH (childLL (childHH (childLH (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHL (childLH (childLL (childHH (childLH (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childLH (childLL (childHH (childLH (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1113013 :
    adaptiveCoverCheck 11 (childHH (childLH (childLL (childHH (childLH (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHH (childLH (childLL (childHH (childLH (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childLH (childLL (childHH (childLH (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111302 :
    adaptiveCoverCheck 12 (childHL (childLL (childHH (childLH (childLH (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childHL (childLL (childHH (childLH (childLH (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL (childHH (childLH (childLH (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111303 :
    adaptiveCoverCheck 12 (childHH (childLL (childHH (childLH (childLH (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childHH (childLL (childHH (childLH (childLH (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL (childHH (childLH (childLH (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1113100 :
    adaptiveCoverCheck 11 (childLL (childLL (childLH (childHH (childLH (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLL (childLL (childLH (childHH (childLH (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLL (childLH (childHH (childLH (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1113101 :
    adaptiveCoverCheck 11 (childLH (childLL (childLH (childHH (childLH (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLH (childLL (childLH (childHH (childLH (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLL (childLH (childHH (childLH (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1113102 :
    adaptiveCoverCheck 11 (childHL (childLL (childLH (childHH (childLH (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHL (childLL (childLH (childHH (childLH (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childLL (childLH (childHH (childLH (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1113103 :
    adaptiveCoverCheck 11 (childHH (childLL (childLH (childHH (childLH (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHH (childLL (childLH (childHH (childLH (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childLL (childLH (childHH (childLH (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1113110 :
    adaptiveCoverCheck 11 (childLL (childLH (childLH (childHH (childLH (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLL (childLH (childLH (childHH (childLH (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLH (childLH (childHH (childLH (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1113111 :
    adaptiveCoverCheck 11 (childLH (childLH (childLH (childHH (childLH (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childLH (childLH (childLH (childHH (childLH (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLH (childLH (childHH (childLH (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1113112 :
    adaptiveCoverCheck 11 (childHL (childLH (childLH (childHH (childLH (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHL (childLH (childLH (childHH (childLH (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childLH (childLH (childHH (childLH (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1113113 :
    adaptiveCoverCheck 11 (childHH (childLH (childLH (childHH (childLH (childLH (childLH e24ThetaBelowRoot))))))) = true := by
  have h : ((childHH (childLH (childLH (childHH (childLH (childLH (childLH e24ThetaBelowRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childLH (childLH (childHH (childLH (childLH (childLH e24ThetaBelowRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111312 :
    adaptiveCoverCheck 12 (childHL (childLH (childHH (childLH (childLH (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childHL (childLH (childHH (childLH (childLH (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childHH (childLH (childLH (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf111313 :
    adaptiveCoverCheck 12 (childHH (childLH (childHH (childLH (childLH (childLH e24ThetaBelowRoot)))))) = true := by
  have h : ((childHH (childLH (childHH (childLH (childLH (childLH e24ThetaBelowRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childHH (childLH (childLH (childLH e24ThetaBelowRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11132 :
    adaptiveCoverCheck 13 (childHL (childHH (childLH (childLH (childLH e24ThetaBelowRoot))))) = true := by
  have h : ((childHL (childHH (childLH (childLH (childLH e24ThetaBelowRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childHH (childLH (childLH (childLH e24ThetaBelowRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11133 :
    adaptiveCoverCheck 13 (childHH (childHH (childLH (childLH (childLH e24ThetaBelowRoot))))) = true := by
  have h : ((childHH (childHH (childLH (childLH (childLH e24ThetaBelowRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childHH (childLH (childLH (childLH e24ThetaBelowRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1120 :
    adaptiveCoverCheck 14 (childLL (childHL (childLH (childLH e24ThetaBelowRoot)))) = true := by
  have h : ((childLL (childHL (childLH (childLH e24ThetaBelowRoot))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 (childLL (childHL (childLH (childLH e24ThetaBelowRoot)))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11210 :
    adaptiveCoverCheck 13 (childLL (childLH (childHL (childLH (childLH e24ThetaBelowRoot))))) = true := by
  have h : ((childLL (childLH (childHL (childLH (childLH e24ThetaBelowRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL (childLH (childHL (childLH (childLH e24ThetaBelowRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11211 :
    adaptiveCoverCheck 13 (childLH (childLH (childHL (childLH (childLH e24ThetaBelowRoot))))) = true := by
  have h : ((childLH (childLH (childHL (childLH (childLH e24ThetaBelowRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH (childLH (childHL (childLH (childLH e24ThetaBelowRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11212 :
    adaptiveCoverCheck 13 (childHL (childLH (childHL (childLH (childLH e24ThetaBelowRoot))))) = true := by
  have h : ((childHL (childLH (childHL (childLH (childLH e24ThetaBelowRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLH (childHL (childLH (childLH e24ThetaBelowRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11213 :
    adaptiveCoverCheck 13 (childHH (childLH (childHL (childLH (childLH e24ThetaBelowRoot))))) = true := by
  have h : ((childHH (childLH (childHL (childLH (childLH e24ThetaBelowRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLH (childHL (childLH (childLH e24ThetaBelowRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1122 :
    adaptiveCoverCheck 14 (childHL (childHL (childLH (childLH e24ThetaBelowRoot)))) = true := by
  have h : ((childHL (childHL (childLH (childLH e24ThetaBelowRoot))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 (childHL (childHL (childLH (childLH e24ThetaBelowRoot)))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1123 :
    adaptiveCoverCheck 14 (childHH (childHL (childLH (childLH e24ThetaBelowRoot)))) = true := by
  have h : ((childHH (childHL (childLH (childLH e24ThetaBelowRoot))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 (childHH (childHL (childLH (childLH e24ThetaBelowRoot)))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11300 :
    adaptiveCoverCheck 13 (childLL (childLL (childHH (childLH (childLH e24ThetaBelowRoot))))) = true := by
  have h : ((childLL (childLL (childHH (childLH (childLH e24ThetaBelowRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL (childLL (childHH (childLH (childLH e24ThetaBelowRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11301 :
    adaptiveCoverCheck 13 (childLH (childLL (childHH (childLH (childLH e24ThetaBelowRoot))))) = true := by
  have h : ((childLH (childLL (childHH (childLH (childLH e24ThetaBelowRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH (childLL (childHH (childLH (childLH e24ThetaBelowRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11302 :
    adaptiveCoverCheck 13 (childHL (childLL (childHH (childLH (childLH e24ThetaBelowRoot))))) = true := by
  have h : ((childHL (childLL (childHH (childLH (childLH e24ThetaBelowRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLL (childHH (childLH (childLH e24ThetaBelowRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11303 :
    adaptiveCoverCheck 13 (childHH (childLL (childHH (childLH (childLH e24ThetaBelowRoot))))) = true := by
  have h : ((childHH (childLL (childHH (childLH (childLH e24ThetaBelowRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLL (childHH (childLH (childLH e24ThetaBelowRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11310 :
    adaptiveCoverCheck 13 (childLL (childLH (childHH (childLH (childLH e24ThetaBelowRoot))))) = true := by
  have h : ((childLL (childLH (childHH (childLH (childLH e24ThetaBelowRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL (childLH (childHH (childLH (childLH e24ThetaBelowRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11311 :
    adaptiveCoverCheck 13 (childLH (childLH (childHH (childLH (childLH e24ThetaBelowRoot))))) = true := by
  have h : ((childLH (childLH (childHH (childLH (childLH e24ThetaBelowRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH (childLH (childHH (childLH (childLH e24ThetaBelowRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11312 :
    adaptiveCoverCheck 13 (childHL (childLH (childHH (childLH (childLH e24ThetaBelowRoot))))) = true := by
  have h : ((childHL (childLH (childHH (childLH (childLH e24ThetaBelowRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLH (childHH (childLH (childLH e24ThetaBelowRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf11313 :
    adaptiveCoverCheck 13 (childHH (childLH (childHH (childLH (childLH e24ThetaBelowRoot))))) = true := by
  have h : ((childHH (childLH (childHH (childLH (childLH e24ThetaBelowRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLH (childHH (childLH (childLH e24ThetaBelowRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1132 :
    adaptiveCoverCheck 14 (childHL (childHH (childLH (childLH e24ThetaBelowRoot)))) = true := by
  have h : ((childHL (childHH (childLH (childLH e24ThetaBelowRoot))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 (childHL (childHH (childLH (childLH e24ThetaBelowRoot)))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1133 :
    adaptiveCoverCheck 14 (childHH (childHH (childLH (childLH e24ThetaBelowRoot)))) = true := by
  have h : ((childHH (childHH (childLH (childLH e24ThetaBelowRoot))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 (childHH (childHH (childLH (childLH e24ThetaBelowRoot)))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf120 :
    adaptiveCoverCheck 15 (childLL (childHL (childLH e24ThetaBelowRoot))) = true := by
  have h : ((childLL (childHL (childLH e24ThetaBelowRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 (childLL (childHL (childLH e24ThetaBelowRoot))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf121 :
    adaptiveCoverCheck 15 (childLH (childHL (childLH e24ThetaBelowRoot))) = true := by
  have h : ((childLH (childHL (childLH e24ThetaBelowRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 (childLH (childHL (childLH e24ThetaBelowRoot))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf122 :
    adaptiveCoverCheck 15 (childHL (childHL (childLH e24ThetaBelowRoot))) = true := by
  have h : ((childHL (childHL (childLH e24ThetaBelowRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 (childHL (childHL (childLH e24ThetaBelowRoot))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf123 :
    adaptiveCoverCheck 15 (childHH (childHL (childLH e24ThetaBelowRoot))) = true := by
  have h : ((childHH (childHL (childLH e24ThetaBelowRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 (childHH (childHL (childLH e24ThetaBelowRoot))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1300 :
    adaptiveCoverCheck 14 (childLL (childLL (childHH (childLH e24ThetaBelowRoot)))) = true := by
  have h : ((childLL (childLL (childHH (childLH e24ThetaBelowRoot))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 (childLL (childLL (childHH (childLH e24ThetaBelowRoot)))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1301 :
    adaptiveCoverCheck 14 (childLH (childLL (childHH (childLH e24ThetaBelowRoot)))) = true := by
  have h : ((childLH (childLL (childHH (childLH e24ThetaBelowRoot))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 (childLH (childLL (childHH (childLH e24ThetaBelowRoot)))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1302 :
    adaptiveCoverCheck 14 (childHL (childLL (childHH (childLH e24ThetaBelowRoot)))) = true := by
  have h : ((childHL (childLL (childHH (childLH e24ThetaBelowRoot))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 (childHL (childLL (childHH (childLH e24ThetaBelowRoot)))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1303 :
    adaptiveCoverCheck 14 (childHH (childLL (childHH (childLH e24ThetaBelowRoot)))) = true := by
  have h : ((childHH (childLL (childHH (childLH e24ThetaBelowRoot))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 (childHH (childLL (childHH (childLH e24ThetaBelowRoot)))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1310 :
    adaptiveCoverCheck 14 (childLL (childLH (childHH (childLH e24ThetaBelowRoot)))) = true := by
  have h : ((childLL (childLH (childHH (childLH e24ThetaBelowRoot))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 (childLL (childLH (childHH (childLH e24ThetaBelowRoot)))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1311 :
    adaptiveCoverCheck 14 (childLH (childLH (childHH (childLH e24ThetaBelowRoot)))) = true := by
  have h : ((childLH (childLH (childHH (childLH e24ThetaBelowRoot))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 (childLH (childLH (childHH (childLH e24ThetaBelowRoot)))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1312 :
    adaptiveCoverCheck 14 (childHL (childLH (childHH (childLH e24ThetaBelowRoot)))) = true := by
  have h : ((childHL (childLH (childHH (childLH e24ThetaBelowRoot))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 (childHL (childLH (childHH (childLH e24ThetaBelowRoot)))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf1313 :
    adaptiveCoverCheck 14 (childHH (childLH (childHH (childLH e24ThetaBelowRoot)))) = true := by
  have h : ((childHH (childLH (childHH (childLH e24ThetaBelowRoot))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 (childHH (childLH (childHH (childLH e24ThetaBelowRoot)))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf132 :
    adaptiveCoverCheck 15 (childHL (childHH (childLH e24ThetaBelowRoot))) = true := by
  have h : ((childHL (childHH (childLH e24ThetaBelowRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 (childHL (childHH (childLH e24ThetaBelowRoot))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf133 :
    adaptiveCoverCheck 15 (childHH (childHH (childLH e24ThetaBelowRoot))) = true := by
  have h : ((childHH (childHH (childLH e24ThetaBelowRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 (childHH (childHH (childLH e24ThetaBelowRoot))) h

theorem e24KC2ThetaBelowLeaf2 :
    adaptiveCoverCheck 17 (childHL e24ThetaBelowRoot) = true := by
  have h : physicallyIrrelevant (childHL e24ThetaBelowRoot) = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_physicallyIrrelevant 17 (childHL e24ThetaBelowRoot) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf300 :
    adaptiveCoverCheck 15 (childLL (childLL (childHH e24ThetaBelowRoot))) = true := by
  have h : ((childLL (childLL (childHH e24ThetaBelowRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 (childLL (childLL (childHH e24ThetaBelowRoot))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf301 :
    adaptiveCoverCheck 15 (childLH (childLL (childHH e24ThetaBelowRoot))) = true := by
  have h : ((childLH (childLL (childHH e24ThetaBelowRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 (childLH (childLL (childHH e24ThetaBelowRoot))) h

theorem e24KC2ThetaBelowLeaf302 :
    adaptiveCoverCheck 15 (childHL (childLL (childHH e24ThetaBelowRoot))) = true := by
  have h : physicallyIrrelevant (childHL (childLL (childHH e24ThetaBelowRoot))) = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_physicallyIrrelevant 15 (childHL (childLL (childHH e24ThetaBelowRoot))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf303 :
    adaptiveCoverCheck 15 (childHH (childLL (childHH e24ThetaBelowRoot))) = true := by
  have h : ((childHH (childLL (childHH e24ThetaBelowRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 (childHH (childLL (childHH e24ThetaBelowRoot))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf310 :
    adaptiveCoverCheck 15 (childLL (childLH (childHH e24ThetaBelowRoot))) = true := by
  have h : ((childLL (childLH (childHH e24ThetaBelowRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 (childLL (childLH (childHH e24ThetaBelowRoot))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf311 :
    adaptiveCoverCheck 15 (childLH (childLH (childHH e24ThetaBelowRoot))) = true := by
  have h : ((childLH (childLH (childHH e24ThetaBelowRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 (childLH (childLH (childHH e24ThetaBelowRoot))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf312 :
    adaptiveCoverCheck 15 (childHL (childLH (childHH e24ThetaBelowRoot))) = true := by
  have h : ((childHL (childLH (childHH e24ThetaBelowRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 (childHL (childLH (childHH e24ThetaBelowRoot))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf313 :
    adaptiveCoverCheck 15 (childHH (childLH (childHH e24ThetaBelowRoot))) = true := by
  have h : ((childHH (childLH (childHH e24ThetaBelowRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 (childHH (childLH (childHH e24ThetaBelowRoot))) h

theorem e24KC2ThetaBelowLeaf32 :
    adaptiveCoverCheck 16 (childHL (childHH e24ThetaBelowRoot)) = true := by
  have h : physicallyIrrelevant (childHL (childHH e24ThetaBelowRoot)) = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_physicallyIrrelevant 16 (childHL (childHH e24ThetaBelowRoot)) h

theorem e24KC2ThetaBelowLeaf330 :
    adaptiveCoverCheck 15 (childLL (childHH (childHH e24ThetaBelowRoot))) = true := by
  have h : physicallyIrrelevant (childLL (childHH (childHH e24ThetaBelowRoot))) = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_physicallyIrrelevant 15 (childLL (childHH (childHH e24ThetaBelowRoot))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaBelowLeaf331 :
    adaptiveCoverCheck 15 (childLH (childHH (childHH e24ThetaBelowRoot))) = true := by
  have h : ((childLH (childHH (childHH e24ThetaBelowRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 (childLH (childHH (childHH e24ThetaBelowRoot))) h

theorem e24KC2ThetaBelowLeaf332 :
    adaptiveCoverCheck 15 (childHL (childHH (childHH e24ThetaBelowRoot))) = true := by
  have h : physicallyIrrelevant (childHL (childHH (childHH e24ThetaBelowRoot))) = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_physicallyIrrelevant 15 (childHL (childHH (childHH e24ThetaBelowRoot))) h

theorem e24KC2ThetaBelowLeaf333 :
    adaptiveCoverCheck 15 (childHH (childHH (childHH e24ThetaBelowRoot))) = true := by
  have h : physicallyIrrelevant (childHH (childHH (childHH e24ThetaBelowRoot))) = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_physicallyIrrelevant 15 (childHH (childHH (childHH e24ThetaBelowRoot))) h

end PartE
end GerverSofa
