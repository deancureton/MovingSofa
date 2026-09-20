import GerverSofa.KernelOnly.PartE.E24KC2ProofHelpers

/-! E24KC6 explicit proof-producing certificate batch. -/
noncomputable section

namespace GerverSofa
namespace PartE

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010221121 :
    adaptiveCoverCheck 9 (childLH (childHL (childLH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL (childLH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childHL (childLH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHL (childLH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childHL (childLH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHL (childLH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childHL (childLH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childHL (childLH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childHL (childLH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childHL (childLH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010221122 :
    adaptiveCoverCheck 9 (childHL (childHL (childLH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL (childLH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childHL (childLH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL (childLH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childHL (childLH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL (childLH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childHL (childLH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL (childLH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHL (childLH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL (childLH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010221123 :
    adaptiveCoverCheck 9 (childHH (childHL (childLH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL (childLH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childHL (childLH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL (childLH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childHL (childLH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL (childLH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childHL (childLH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL (childLH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHL (childLH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL (childLH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010221130 :
    adaptiveCoverCheck 9 (childLL (childHH (childLH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH (childLH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childHH (childLH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHH (childLH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childHH (childLH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHH (childLH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childHH (childLH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childHH (childLH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childHH (childLH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childHH (childLH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010221131 :
    adaptiveCoverCheck 9 (childLH (childHH (childLH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH (childLH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childHH (childLH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHH (childLH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childHH (childLH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHH (childLH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childHH (childLH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childHH (childLH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childHH (childLH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childHH (childLH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010221132 :
    adaptiveCoverCheck 9 (childHL (childHH (childLH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH (childLH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childHH (childLH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH (childLH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childHH (childLH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH (childLH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childHH (childLH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH (childLH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHH (childLH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH (childLH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010221133 :
    adaptiveCoverCheck 9 (childHH (childHH (childLH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH (childLH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childHH (childLH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH (childLH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childHH (childLH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH (childLH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childHH (childLH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH (childLH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHH (childLH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH (childLH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010221200 :
    adaptiveCoverCheck 9 (childLL (childLL (childHL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLL (childHL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childLL (childHL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLL (childHL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childLL (childHL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLL (childHL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childLL (childHL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLL (childHL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childLL (childHL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLL (childHL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010221201 :
    adaptiveCoverCheck 9 (childLH (childLL (childHL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLL (childHL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childLL (childHL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLL (childHL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childLL (childHL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLL (childHL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childLL (childHL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLL (childHL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childLL (childHL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLL (childHL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010221210 :
    adaptiveCoverCheck 9 (childLL (childLH (childHL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLH (childHL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childLH (childHL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLH (childHL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childLH (childHL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLH (childHL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childLH (childHL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLH (childHL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childLH (childHL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLH (childHL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010221211 :
    adaptiveCoverCheck 9 (childLH (childLH (childHL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLH (childHL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childLH (childHL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLH (childHL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childLH (childHL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLH (childHL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childLH (childHL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLH (childHL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childLH (childHL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLH (childHL (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010221300 :
    adaptiveCoverCheck 9 (childLL (childLL (childHH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLL (childHH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childLL (childHH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLL (childHH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childLL (childHH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLL (childHH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childLL (childHH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLL (childHH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childLL (childHH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLL (childHH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010221301 :
    adaptiveCoverCheck 9 (childLH (childLL (childHH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLL (childHH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childLL (childHH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLL (childHH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childLL (childHH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLL (childHH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childLL (childHH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLL (childHH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childLL (childHH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLL (childHH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010221310 :
    adaptiveCoverCheck 9 (childLL (childLH (childHH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLH (childHH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childLH (childHH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLH (childHH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childLH (childHH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLH (childHH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childLH (childHH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLH (childHH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childLH (childHH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLH (childHH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010221311 :
    adaptiveCoverCheck 9 (childLH (childLH (childHH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLH (childHH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childLH (childHH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLH (childHH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childLH (childHH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLH (childHH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childLH (childHH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLH (childHH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childLH (childHH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLH (childHH (childLH (childHL (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010230020 :
    adaptiveCoverCheck 9 (childLL (childHL (childLL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL (childLL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childHL (childLL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHL (childLL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childHL (childLL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHL (childLL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childHL (childLL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childHL (childLL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childHL (childLL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childHL (childLL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010230021 :
    adaptiveCoverCheck 9 (childLH (childHL (childLL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL (childLL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childHL (childLL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHL (childLL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childHL (childLL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHL (childLL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childHL (childLL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childHL (childLL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childHL (childLL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childHL (childLL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010230022 :
    adaptiveCoverCheck 9 (childHL (childHL (childLL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL (childLL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childHL (childLL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL (childLL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childHL (childLL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL (childLL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childHL (childLL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL (childLL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHL (childLL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL (childLL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010230023 :
    adaptiveCoverCheck 9 (childHH (childHL (childLL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL (childLL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childHL (childLL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL (childLL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childHL (childLL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL (childLL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childHL (childLL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL (childLL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHL (childLL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL (childLL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010230030 :
    adaptiveCoverCheck 9 (childLL (childHH (childLL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH (childLL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childHH (childLL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHH (childLL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childHH (childLL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHH (childLL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childHH (childLL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childHH (childLL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childHH (childLL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childHH (childLL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010230031 :
    adaptiveCoverCheck 9 (childLH (childHH (childLL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH (childLL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childHH (childLL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHH (childLL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childHH (childLL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHH (childLL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childHH (childLL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childHH (childLL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childHH (childLL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childHH (childLL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010230032 :
    adaptiveCoverCheck 9 (childHL (childHH (childLL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH (childLL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childHH (childLL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH (childLL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childHH (childLL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH (childLL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childHH (childLL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH (childLL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHH (childLL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH (childLL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010230033 :
    adaptiveCoverCheck 9 (childHH (childHH (childLL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH (childLL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childHH (childLL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH (childLL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childHH (childLL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH (childLL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childHH (childLL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH (childLL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHH (childLL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH (childLL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010230120 :
    adaptiveCoverCheck 9 (childLL (childHL (childLH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL (childLH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childHL (childLH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHL (childLH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childHL (childLH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHL (childLH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childHL (childLH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childHL (childLH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childHL (childLH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childHL (childLH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010230121 :
    adaptiveCoverCheck 9 (childLH (childHL (childLH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL (childLH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childHL (childLH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHL (childLH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childHL (childLH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHL (childLH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childHL (childLH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childHL (childLH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childHL (childLH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childHL (childLH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010230122 :
    adaptiveCoverCheck 9 (childHL (childHL (childLH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL (childLH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childHL (childLH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL (childLH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childHL (childLH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL (childLH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childHL (childLH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL (childLH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHL (childLH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL (childLH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010230123 :
    adaptiveCoverCheck 9 (childHH (childHL (childLH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL (childLH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childHL (childLH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL (childLH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childHL (childLH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL (childLH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childHL (childLH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL (childLH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHL (childLH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL (childLH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010230130 :
    adaptiveCoverCheck 9 (childLL (childHH (childLH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH (childLH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childHH (childLH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHH (childLH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childHH (childLH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHH (childLH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childHH (childLH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childHH (childLH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childHH (childLH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childHH (childLH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010230131 :
    adaptiveCoverCheck 9 (childLH (childHH (childLH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH (childLH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childHH (childLH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHH (childLH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childHH (childLH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHH (childLH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childHH (childLH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childHH (childLH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childHH (childLH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childHH (childLH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010230132 :
    adaptiveCoverCheck 9 (childHL (childHH (childLH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH (childLH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childHH (childLH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH (childLH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childHH (childLH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH (childLH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childHH (childLH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH (childLH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHH (childLH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH (childLH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010230133 :
    adaptiveCoverCheck 9 (childHH (childHH (childLH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH (childLH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childHH (childLH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH (childLH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childHH (childLH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH (childLH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childHH (childLH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH (childLH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHH (childLH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH (childLH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010230200 :
    adaptiveCoverCheck 9 (childLL (childLL (childHL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLL (childHL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childLL (childHL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLL (childHL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childLL (childHL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLL (childHL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childLL (childHL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLL (childHL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childLL (childHL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLL (childHL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010230201 :
    adaptiveCoverCheck 9 (childLH (childLL (childHL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLL (childHL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childLL (childHL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLL (childHL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childLL (childHL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLL (childHL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childLL (childHL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLL (childHL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childLL (childHL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLL (childHL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010230210 :
    adaptiveCoverCheck 9 (childLL (childLH (childHL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLH (childHL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childLH (childHL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLH (childHL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childLH (childHL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLH (childHL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childLH (childHL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLH (childHL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childLH (childHL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLH (childHL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010230211 :
    adaptiveCoverCheck 9 (childLH (childLH (childHL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLH (childHL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childLH (childHL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLH (childHL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childLH (childHL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLH (childHL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childLH (childHL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLH (childHL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childLH (childHL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLH (childHL (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010230300 :
    adaptiveCoverCheck 9 (childLL (childLL (childHH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLL (childHH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childLL (childHH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLL (childHH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childLL (childHH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLL (childHH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childLL (childHH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLL (childHH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childLL (childHH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLL (childHH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010230301 :
    adaptiveCoverCheck 9 (childLH (childLL (childHH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLL (childHH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childLL (childHH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLL (childHH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childLL (childHH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLL (childHH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childLL (childHH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLL (childHH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childLL (childHH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLL (childHH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010230310 :
    adaptiveCoverCheck 9 (childLL (childLH (childHH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLH (childHH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childLH (childHH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLH (childHH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childLH (childHH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLH (childHH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childLH (childHH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLH (childHH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childLH (childHH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLH (childHH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010230311 :
    adaptiveCoverCheck 9 (childLH (childLH (childHH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLH (childHH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childLH (childHH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLH (childHH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childLH (childHH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLH (childHH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childLH (childHH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLH (childHH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childLH (childHH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLH (childHH (childLL (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010231020 :
    adaptiveCoverCheck 9 (childLL (childHL (childLL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL (childLL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childHL (childLL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHL (childLL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childHL (childLL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHL (childLL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childHL (childLL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childHL (childLL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childHL (childLL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childHL (childLL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010231021 :
    adaptiveCoverCheck 9 (childLH (childHL (childLL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL (childLL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childHL (childLL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHL (childLL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childHL (childLL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHL (childLL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childHL (childLL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childHL (childLL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childHL (childLL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childHL (childLL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010231022 :
    adaptiveCoverCheck 9 (childHL (childHL (childLL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL (childLL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childHL (childLL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL (childLL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childHL (childLL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL (childLL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childHL (childLL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL (childLL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHL (childLL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL (childLL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010231023 :
    adaptiveCoverCheck 9 (childHH (childHL (childLL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL (childLL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childHL (childLL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL (childLL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childHL (childLL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL (childLL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childHL (childLL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL (childLL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHL (childLL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL (childLL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010231030 :
    adaptiveCoverCheck 9 (childLL (childHH (childLL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH (childLL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childHH (childLL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHH (childLL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childHH (childLL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHH (childLL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childHH (childLL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childHH (childLL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childHH (childLL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childHH (childLL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010231031 :
    adaptiveCoverCheck 9 (childLH (childHH (childLL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH (childLL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childHH (childLL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHH (childLL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childHH (childLL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHH (childLL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childHH (childLL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childHH (childLL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childHH (childLL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childHH (childLL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010231032 :
    adaptiveCoverCheck 9 (childHL (childHH (childLL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH (childLL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childHH (childLL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH (childLL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childHH (childLL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH (childLL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childHH (childLL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH (childLL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHH (childLL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH (childLL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010231033 :
    adaptiveCoverCheck 9 (childHH (childHH (childLL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH (childLL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childHH (childLL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH (childLL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childHH (childLL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH (childLL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childHH (childLL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH (childLL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHH (childLL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH (childLL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010231120 :
    adaptiveCoverCheck 9 (childLL (childHL (childLH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL (childLH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childHL (childLH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHL (childLH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childHL (childLH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHL (childLH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childHL (childLH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childHL (childLH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childHL (childLH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childHL (childLH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010231121 :
    adaptiveCoverCheck 9 (childLH (childHL (childLH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL (childLH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childHL (childLH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHL (childLH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childHL (childLH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHL (childLH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childHL (childLH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childHL (childLH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childHL (childLH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childHL (childLH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010231122 :
    adaptiveCoverCheck 9 (childHL (childHL (childLH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL (childLH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childHL (childLH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL (childLH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childHL (childLH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL (childLH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childHL (childLH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL (childLH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHL (childLH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL (childLH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010231123 :
    adaptiveCoverCheck 9 (childHH (childHL (childLH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL (childLH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childHL (childLH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL (childLH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childHL (childLH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL (childLH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childHL (childLH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL (childLH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHL (childLH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL (childLH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010231130 :
    adaptiveCoverCheck 9 (childLL (childHH (childLH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH (childLH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childHH (childLH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHH (childLH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childHH (childLH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHH (childLH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childHH (childLH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childHH (childLH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childHH (childLH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childHH (childLH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010231131 :
    adaptiveCoverCheck 9 (childLH (childHH (childLH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH (childLH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childHH (childLH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHH (childLH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childHH (childLH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHH (childLH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childHH (childLH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childHH (childLH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childHH (childLH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childHH (childLH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010231132 :
    adaptiveCoverCheck 9 (childHL (childHH (childLH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH (childLH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childHH (childLH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH (childLH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childHH (childLH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH (childLH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childHH (childLH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH (childLH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHH (childLH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH (childLH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010231133 :
    adaptiveCoverCheck 9 (childHH (childHH (childLH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH (childLH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childHH (childLH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH (childLH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childHH (childLH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH (childLH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childHH (childLH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH (childLH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHH (childLH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH (childLH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010231200 :
    adaptiveCoverCheck 9 (childLL (childLL (childHL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLL (childHL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childLL (childHL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLL (childHL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childLL (childHL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLL (childHL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childLL (childHL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLL (childHL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childLL (childHL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLL (childHL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010231201 :
    adaptiveCoverCheck 9 (childLH (childLL (childHL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLL (childHL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childLL (childHL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLL (childHL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childLL (childHL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLL (childHL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childLL (childHL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLL (childHL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childLL (childHL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLL (childHL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010231210 :
    adaptiveCoverCheck 9 (childLL (childLH (childHL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLH (childHL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childLH (childHL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLH (childHL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childLH (childHL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLH (childHL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childLH (childHL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLH (childHL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childLH (childHL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLH (childHL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010231211 :
    adaptiveCoverCheck 9 (childLH (childLH (childHL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLH (childHL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childLH (childHL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLH (childHL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childLH (childHL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLH (childHL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childLH (childHL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLH (childHL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childLH (childHL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLH (childHL (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010231300 :
    adaptiveCoverCheck 9 (childLL (childLL (childHH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLL (childHH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childLL (childHH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLL (childHH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childLL (childHH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLL (childHH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childLL (childHH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLL (childHH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childLL (childHH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLL (childHH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010231301 :
    adaptiveCoverCheck 9 (childLH (childLL (childHH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLL (childHH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childLL (childHH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLL (childHH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childLL (childHH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLL (childHH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childLL (childHH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLL (childHH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childLL (childHH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLL (childHH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010231310 :
    adaptiveCoverCheck 9 (childLL (childLH (childHH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLH (childHH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childLH (childHH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLH (childHH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childLH (childHH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLH (childHH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childLH (childHH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLH (childHH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childLH (childHH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLH (childHH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010231311 :
    adaptiveCoverCheck 9 (childLH (childLH (childHH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLH (childHH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childLH (childHH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLH (childHH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childLH (childHH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLH (childHH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childLH (childHH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLH (childHH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childLH (childHH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLH (childHH (childLH (childHH (childHL (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010320020 :
    adaptiveCoverCheck 9 (childLL (childHL (childLL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL (childLL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childHL (childLL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHL (childLL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childHL (childLL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHL (childLL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childHL (childLL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childHL (childLL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childHL (childLL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childHL (childLL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010320021 :
    adaptiveCoverCheck 9 (childLH (childHL (childLL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL (childLL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childHL (childLL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHL (childLL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childHL (childLL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHL (childLL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childHL (childLL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childHL (childLL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childHL (childLL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childHL (childLL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010320022 :
    adaptiveCoverCheck 9 (childHL (childHL (childLL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL (childLL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childHL (childLL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL (childLL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childHL (childLL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL (childLL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childHL (childLL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL (childLL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHL (childLL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL (childLL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010320023 :
    adaptiveCoverCheck 9 (childHH (childHL (childLL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL (childLL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childHL (childLL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL (childLL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childHL (childLL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL (childLL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childHL (childLL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL (childLL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHL (childLL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL (childLL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010320030 :
    adaptiveCoverCheck 9 (childLL (childHH (childLL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH (childLL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childHH (childLL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHH (childLL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childHH (childLL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHH (childLL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childHH (childLL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childHH (childLL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childHH (childLL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childHH (childLL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010320031 :
    adaptiveCoverCheck 9 (childLH (childHH (childLL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH (childLL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childHH (childLL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHH (childLL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childHH (childLL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHH (childLL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childHH (childLL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childHH (childLL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childHH (childLL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childHH (childLL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010320032 :
    adaptiveCoverCheck 9 (childHL (childHH (childLL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH (childLL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childHH (childLL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH (childLL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childHH (childLL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH (childLL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childHH (childLL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH (childLL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHH (childLL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH (childLL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010320033 :
    adaptiveCoverCheck 9 (childHH (childHH (childLL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH (childLL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childHH (childLL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH (childLL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childHH (childLL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH (childLL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childHH (childLL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH (childLL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHH (childLL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH (childLL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010320120 :
    adaptiveCoverCheck 9 (childLL (childHL (childLH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL (childLH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childHL (childLH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHL (childLH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childHL (childLH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHL (childLH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childHL (childLH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childHL (childLH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childHL (childLH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childHL (childLH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010320121 :
    adaptiveCoverCheck 9 (childLH (childHL (childLH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL (childLH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childHL (childLH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHL (childLH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childHL (childLH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHL (childLH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childHL (childLH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childHL (childLH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childHL (childLH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childHL (childLH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010320122 :
    adaptiveCoverCheck 9 (childHL (childHL (childLH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL (childLH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childHL (childLH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL (childLH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childHL (childLH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL (childLH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childHL (childLH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL (childLH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHL (childLH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL (childLH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010320123 :
    adaptiveCoverCheck 9 (childHH (childHL (childLH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL (childLH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childHL (childLH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL (childLH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childHL (childLH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL (childLH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childHL (childLH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL (childLH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHL (childLH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL (childLH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010320130 :
    adaptiveCoverCheck 9 (childLL (childHH (childLH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH (childLH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childHH (childLH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHH (childLH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childHH (childLH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHH (childLH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childHH (childLH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childHH (childLH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childHH (childLH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childHH (childLH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010320131 :
    adaptiveCoverCheck 9 (childLH (childHH (childLH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH (childLH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childHH (childLH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHH (childLH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childHH (childLH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHH (childLH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childHH (childLH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childHH (childLH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childHH (childLH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childHH (childLH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010320132 :
    adaptiveCoverCheck 9 (childHL (childHH (childLH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH (childLH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childHH (childLH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH (childLH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childHH (childLH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH (childLH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childHH (childLH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH (childLH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHH (childLH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH (childLH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010320133 :
    adaptiveCoverCheck 9 (childHH (childHH (childLH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH (childLH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childHH (childLH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH (childLH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childHH (childLH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH (childLH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childHH (childLH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH (childLH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHH (childLH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH (childLH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010320200 :
    adaptiveCoverCheck 9 (childLL (childLL (childHL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLL (childHL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childLL (childHL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLL (childHL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childLL (childHL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLL (childHL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childLL (childHL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLL (childHL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childLL (childHL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLL (childHL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010320201 :
    adaptiveCoverCheck 9 (childLH (childLL (childHL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLL (childHL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childLL (childHL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLL (childHL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childLL (childHL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLL (childHL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childLL (childHL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLL (childHL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childLL (childHL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLL (childHL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010320210 :
    adaptiveCoverCheck 9 (childLL (childLH (childHL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLH (childHL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childLH (childHL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLH (childHL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childLH (childHL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLH (childHL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childLH (childHL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLH (childHL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childLH (childHL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLH (childHL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010320211 :
    adaptiveCoverCheck 9 (childLH (childLH (childHL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLH (childHL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childLH (childHL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLH (childHL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childLH (childHL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLH (childHL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childLH (childHL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLH (childHL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childLH (childHL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLH (childHL (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010320300 :
    adaptiveCoverCheck 9 (childLL (childLL (childHH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLL (childHH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childLL (childHH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLL (childHH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childLL (childHH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLL (childHH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childLL (childHH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLL (childHH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childLL (childHH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLL (childHH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010320301 :
    adaptiveCoverCheck 9 (childLH (childLL (childHH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLL (childHH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childLL (childHH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLL (childHH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childLL (childHH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLL (childHH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childLL (childHH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLL (childHH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childLL (childHH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLL (childHH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010320310 :
    adaptiveCoverCheck 9 (childLL (childLH (childHH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLH (childHH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childLH (childHH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLH (childHH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childLH (childHH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLH (childHH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childLH (childHH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLH (childHH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childLH (childHH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLH (childHH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010320311 :
    adaptiveCoverCheck 9 (childLH (childLH (childHH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLH (childHH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childLH (childHH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLH (childHH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childLH (childHH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLH (childHH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childLH (childHH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLH (childHH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childLH (childHH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLH (childHH (childLL (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010321020 :
    adaptiveCoverCheck 9 (childLL (childHL (childLL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL (childLL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childHL (childLL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHL (childLL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childHL (childLL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHL (childLL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childHL (childLL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childHL (childLL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childHL (childLL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childHL (childLL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010321021 :
    adaptiveCoverCheck 9 (childLH (childHL (childLL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL (childLL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childHL (childLL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHL (childLL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childHL (childLL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHL (childLL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childHL (childLL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childHL (childLL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childHL (childLL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childHL (childLL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010321022 :
    adaptiveCoverCheck 9 (childHL (childHL (childLL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL (childLL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childHL (childLL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL (childLL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childHL (childLL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL (childLL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childHL (childLL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL (childLL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHL (childLL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL (childLL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010321023 :
    adaptiveCoverCheck 9 (childHH (childHL (childLL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL (childLL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childHL (childLL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL (childLL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childHL (childLL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL (childLL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childHL (childLL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL (childLL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHL (childLL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL (childLL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010321030 :
    adaptiveCoverCheck 9 (childLL (childHH (childLL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH (childLL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childHH (childLL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHH (childLL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childHH (childLL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHH (childLL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childHH (childLL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childHH (childLL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childHH (childLL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childHH (childLL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010321031 :
    adaptiveCoverCheck 9 (childLH (childHH (childLL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH (childLL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childHH (childLL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHH (childLL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childHH (childLL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHH (childLL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childHH (childLL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childHH (childLL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childHH (childLL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childHH (childLL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010321032 :
    adaptiveCoverCheck 9 (childHL (childHH (childLL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH (childLL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childHH (childLL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH (childLL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childHH (childLL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH (childLL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childHH (childLL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH (childLL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHH (childLL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH (childLL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010321033 :
    adaptiveCoverCheck 9 (childHH (childHH (childLL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH (childLL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childHH (childLL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH (childLL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childHH (childLL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH (childLL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childHH (childLL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH (childLL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHH (childLL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH (childLL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010321120 :
    adaptiveCoverCheck 9 (childLL (childHL (childLH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL (childLH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childHL (childLH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHL (childLH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childHL (childLH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHL (childLH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childHL (childLH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childHL (childLH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childHL (childLH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childHL (childLH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010321121 :
    adaptiveCoverCheck 9 (childLH (childHL (childLH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL (childLH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childHL (childLH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHL (childLH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childHL (childLH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHL (childLH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childHL (childLH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childHL (childLH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childHL (childLH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childHL (childLH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010321122 :
    adaptiveCoverCheck 9 (childHL (childHL (childLH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL (childLH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childHL (childLH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL (childLH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childHL (childLH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL (childLH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childHL (childLH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL (childLH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHL (childLH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL (childLH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010321123 :
    adaptiveCoverCheck 9 (childHH (childHL (childLH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL (childLH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childHL (childLH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL (childLH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childHL (childLH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL (childLH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childHL (childLH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL (childLH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHL (childLH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL (childLH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010321130 :
    adaptiveCoverCheck 9 (childLL (childHH (childLH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH (childLH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childHH (childLH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHH (childLH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childHH (childLH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHH (childLH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childHH (childLH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childHH (childLH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childHH (childLH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childHH (childLH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010321131 :
    adaptiveCoverCheck 9 (childLH (childHH (childLH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH (childLH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childHH (childLH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHH (childLH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childHH (childLH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHH (childLH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childHH (childLH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childHH (childLH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childHH (childLH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childHH (childLH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010321132 :
    adaptiveCoverCheck 9 (childHL (childHH (childLH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH (childLH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childHH (childLH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH (childLH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childHH (childLH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH (childLH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childHH (childLH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH (childLH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHH (childLH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH (childLH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010321133 :
    adaptiveCoverCheck 9 (childHH (childHH (childLH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH (childLH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childHH (childLH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH (childLH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childHH (childLH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH (childLH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childHH (childLH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH (childLH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHH (childLH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH (childLH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010321200 :
    adaptiveCoverCheck 9 (childLL (childLL (childHL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLL (childHL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childLL (childHL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLL (childHL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childLL (childHL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLL (childHL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childLL (childHL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLL (childHL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childLL (childHL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLL (childHL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010321201 :
    adaptiveCoverCheck 9 (childLH (childLL (childHL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLL (childHL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childLL (childHL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLL (childHL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childLL (childHL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLL (childHL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childLL (childHL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLL (childHL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childLL (childHL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLL (childHL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010321210 :
    adaptiveCoverCheck 9 (childLL (childLH (childHL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLH (childHL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childLH (childHL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLH (childHL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childLH (childHL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLH (childHL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childLH (childHL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLH (childHL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childLH (childHL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLH (childHL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010321211 :
    adaptiveCoverCheck 9 (childLH (childLH (childHL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLH (childHL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childLH (childHL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLH (childHL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childLH (childHL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLH (childHL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childLH (childHL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLH (childHL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childLH (childHL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLH (childHL (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010321300 :
    adaptiveCoverCheck 9 (childLL (childLL (childHH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLL (childHH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childLL (childHH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLL (childHH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childLL (childHH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLL (childHH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childLL (childHH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLL (childHH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childLL (childHH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLL (childHH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010321301 :
    adaptiveCoverCheck 9 (childLH (childLL (childHH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLL (childHH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childLL (childHH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLL (childHH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childLL (childHH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLL (childHH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childLL (childHH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLL (childHH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childLL (childHH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLL (childHH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010321310 :
    adaptiveCoverCheck 9 (childLL (childLH (childHH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLH (childHH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childLH (childHH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLH (childHH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childLH (childHH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLH (childHH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childLH (childHH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLH (childHH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childLH (childHH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLH (childHH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010321311 :
    adaptiveCoverCheck 9 (childLH (childLH (childHH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLH (childHH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childLH (childHH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLH (childHH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childLH (childHH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLH (childHH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childLH (childHH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLH (childHH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childLH (childHH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLH (childHH (childLH (childHL (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010330020 :
    adaptiveCoverCheck 9 (childLL (childHL (childLL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL (childLL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childHL (childLL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHL (childLL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childHL (childLL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHL (childLL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childHL (childLL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childHL (childLL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childHL (childLL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childHL (childLL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010330021 :
    adaptiveCoverCheck 9 (childLH (childHL (childLL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL (childLL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childHL (childLL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHL (childLL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childHL (childLL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHL (childLL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childHL (childLL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childHL (childLL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childHL (childLL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childHL (childLL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010330022 :
    adaptiveCoverCheck 9 (childHL (childHL (childLL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL (childLL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childHL (childLL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL (childLL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childHL (childLL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL (childLL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childHL (childLL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL (childLL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHL (childLL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL (childLL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010330023 :
    adaptiveCoverCheck 9 (childHH (childHL (childLL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL (childLL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childHL (childLL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL (childLL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childHL (childLL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL (childLL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childHL (childLL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL (childLL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHL (childLL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL (childLL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010330030 :
    adaptiveCoverCheck 9 (childLL (childHH (childLL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH (childLL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childHH (childLL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHH (childLL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childHH (childLL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHH (childLL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childHH (childLL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childHH (childLL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childHH (childLL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childHH (childLL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010330031 :
    adaptiveCoverCheck 9 (childLH (childHH (childLL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH (childLL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childHH (childLL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHH (childLL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childHH (childLL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHH (childLL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childHH (childLL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childHH (childLL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childHH (childLL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childHH (childLL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010330032 :
    adaptiveCoverCheck 9 (childHL (childHH (childLL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH (childLL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childHH (childLL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH (childLL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childHH (childLL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH (childLL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childHH (childLL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH (childLL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHH (childLL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH (childLL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010330033 :
    adaptiveCoverCheck 9 (childHH (childHH (childLL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH (childLL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childHH (childLL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH (childLL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childHH (childLL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH (childLL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childHH (childLL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH (childLL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHH (childLL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH (childLL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010330120 :
    adaptiveCoverCheck 9 (childLL (childHL (childLH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL (childLH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childHL (childLH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHL (childLH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childHL (childLH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHL (childLH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childHL (childLH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childHL (childLH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childHL (childLH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childHL (childLH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010330121 :
    adaptiveCoverCheck 9 (childLH (childHL (childLH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL (childLH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childHL (childLH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHL (childLH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childHL (childLH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHL (childLH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childHL (childLH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childHL (childLH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childHL (childLH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childHL (childLH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010330122 :
    adaptiveCoverCheck 9 (childHL (childHL (childLH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL (childLH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childHL (childLH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL (childLH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childHL (childLH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL (childLH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childHL (childLH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL (childLH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHL (childLH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL (childLH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010330123 :
    adaptiveCoverCheck 9 (childHH (childHL (childLH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL (childLH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childHL (childLH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL (childLH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childHL (childLH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL (childLH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childHL (childLH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL (childLH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHL (childLH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL (childLH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010330130 :
    adaptiveCoverCheck 9 (childLL (childHH (childLH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH (childLH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childHH (childLH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHH (childLH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childHH (childLH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHH (childLH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childHH (childLH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childHH (childLH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childHH (childLH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childHH (childLH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010330131 :
    adaptiveCoverCheck 9 (childLH (childHH (childLH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH (childLH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childHH (childLH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHH (childLH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childHH (childLH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHH (childLH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childHH (childLH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childHH (childLH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childHH (childLH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childHH (childLH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010330132 :
    adaptiveCoverCheck 9 (childHL (childHH (childLH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH (childLH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childHH (childLH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH (childLH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childHH (childLH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH (childLH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childHH (childLH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH (childLH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHH (childLH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH (childLH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010330133 :
    adaptiveCoverCheck 9 (childHH (childHH (childLH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH (childLH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childHH (childLH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH (childLH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childHH (childLH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH (childLH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childHH (childLH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH (childLH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHH (childLH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH (childLH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010330200 :
    adaptiveCoverCheck 9 (childLL (childLL (childHL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLL (childHL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childLL (childHL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLL (childHL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childLL (childHL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLL (childHL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childLL (childHL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLL (childHL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childLL (childHL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLL (childHL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010330201 :
    adaptiveCoverCheck 9 (childLH (childLL (childHL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLL (childHL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childLL (childHL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLL (childHL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childLL (childHL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLL (childHL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childLL (childHL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLL (childHL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childLL (childHL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLL (childHL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010330210 :
    adaptiveCoverCheck 9 (childLL (childLH (childHL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLH (childHL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childLH (childHL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLH (childHL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childLH (childHL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLH (childHL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childLH (childHL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLH (childHL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childLH (childHL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLH (childHL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010330211 :
    adaptiveCoverCheck 9 (childLH (childLH (childHL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLH (childHL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childLH (childHL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLH (childHL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childLH (childHL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLH (childHL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childLH (childHL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLH (childHL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childLH (childHL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLH (childHL (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010330300 :
    adaptiveCoverCheck 9 (childLL (childLL (childHH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLL (childHH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childLL (childHH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLL (childHH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childLL (childHH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLL (childHH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childLL (childHH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLL (childHH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childLL (childHH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLL (childHH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010330301 :
    adaptiveCoverCheck 9 (childLH (childLL (childHH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLL (childHH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childLL (childHH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLL (childHH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childLL (childHH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLL (childHH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childLL (childHH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLL (childHH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childLL (childHH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLL (childHH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010330310 :
    adaptiveCoverCheck 9 (childLL (childLH (childHH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLH (childHH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childLH (childHH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLH (childHH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childLH (childHH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLH (childHH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childLH (childHH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLH (childHH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childLH (childHH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLH (childHH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010330311 :
    adaptiveCoverCheck 9 (childLH (childLH (childHH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLH (childHH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childLH (childHH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLH (childHH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childLH (childHH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLH (childHH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childLH (childHH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLH (childHH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childLH (childHH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLH (childHH (childLL (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010331020 :
    adaptiveCoverCheck 9 (childLL (childHL (childLL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL (childLL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childHL (childLL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHL (childLL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childHL (childLL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHL (childLL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childHL (childLL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childHL (childLL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childHL (childLL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childHL (childLL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010331021 :
    adaptiveCoverCheck 9 (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childHL (childLL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010331022 :
    adaptiveCoverCheck 9 (childHL (childHL (childLL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL (childLL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childHL (childLL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL (childLL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childHL (childLL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL (childLL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childHL (childLL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL (childLL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHL (childLL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL (childLL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010331023 :
    adaptiveCoverCheck 9 (childHH (childHL (childLL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL (childLL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childHL (childLL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL (childLL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childHL (childLL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL (childLL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childHL (childLL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL (childLL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHL (childLL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL (childLL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010331030 :
    adaptiveCoverCheck 9 (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childHH (childLL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010331031 :
    adaptiveCoverCheck 9 (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childHH (childLL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010331032 :
    adaptiveCoverCheck 9 (childHL (childHH (childLL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH (childLL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childHH (childLL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH (childLL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childHH (childLL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH (childLL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childHH (childLL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH (childLL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHH (childLL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH (childLL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010331033 :
    adaptiveCoverCheck 9 (childHH (childHH (childLL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH (childLL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childHH (childLL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH (childLL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childHH (childLL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH (childLL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childHH (childLL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH (childLL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHH (childLL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH (childLL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010331120 :
    adaptiveCoverCheck 9 (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childHL (childLH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010331121 :
    adaptiveCoverCheck 9 (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childHL (childLH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010331122 :
    adaptiveCoverCheck 9 (childHL (childHL (childLH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL (childLH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childHL (childLH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL (childLH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childHL (childLH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL (childLH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childHL (childLH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL (childLH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHL (childLH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL (childLH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010331123 :
    adaptiveCoverCheck 9 (childHH (childHL (childLH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL (childLH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childHL (childLH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL (childLH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childHL (childLH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL (childLH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childHL (childLH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL (childLH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHL (childLH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL (childLH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010331130 :
    adaptiveCoverCheck 9 (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childHH (childLH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010331131 :
    adaptiveCoverCheck 9 (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childHH (childLH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010331132 :
    adaptiveCoverCheck 9 (childHL (childHH (childLH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH (childLH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childHH (childLH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH (childLH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childHH (childLH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH (childLH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childHH (childLH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH (childLH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHH (childLH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH (childLH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010331133 :
    adaptiveCoverCheck 9 (childHH (childHH (childLH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH (childLH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childHH (childLH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH (childLH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childHH (childLH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH (childLH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childHH (childLH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH (childLH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHH (childLH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH (childLH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010331200 :
    adaptiveCoverCheck 9 (childLL (childLL (childHL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLL (childHL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childLL (childHL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLL (childHL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childLL (childHL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLL (childHL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childLL (childHL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLL (childHL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childLL (childHL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLL (childHL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010331201 :
    adaptiveCoverCheck 9 (childLH (childLL (childHL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLL (childHL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childLL (childHL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLL (childHL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childLL (childHL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLL (childHL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childLL (childHL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLL (childHL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childLL (childHL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLL (childHL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010331210 :
    adaptiveCoverCheck 9 (childLL (childLH (childHL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLH (childHL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childLH (childHL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLH (childHL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childLH (childHL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLH (childHL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childLH (childHL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLH (childHL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childLH (childHL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLH (childHL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010331211 :
    adaptiveCoverCheck 9 (childLH (childLH (childHL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLH (childHL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childLH (childHL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLH (childHL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childLH (childHL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLH (childHL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childLH (childHL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLH (childHL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childLH (childHL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLH (childHL (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010331300 :
    adaptiveCoverCheck 9 (childLL (childLL (childHH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLL (childHH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childLL (childHH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLL (childHH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childLL (childHH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLL (childHH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childLL (childHH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLL (childHH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childLL (childHH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLL (childHH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010331301 :
    adaptiveCoverCheck 9 (childLH (childLL (childHH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLL (childHH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childLL (childHH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLL (childHH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childLL (childHH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLL (childHH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childLL (childHH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLL (childHH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childLL (childHH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLL (childHH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010331310 :
    adaptiveCoverCheck 9 (childLL (childLH (childHH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLH (childHH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childLH (childHH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLH (childHH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childLH (childHH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLH (childHH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childLH (childHH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLH (childHH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childLH (childHH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLH (childHH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0010331311 :
    adaptiveCoverCheck 9 (childLH (childLH (childHH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLH (childHH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childLH (childHH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLH (childHH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childLH (childHH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLH (childHH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childLH (childHH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLH (childHH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childLH (childHH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLH (childHH (childLH (childHH (childHH (childLL (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011220020 :
    adaptiveCoverCheck 9 (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childHL (childLL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011220021 :
    adaptiveCoverCheck 9 (childLH (childHL (childLL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL (childLL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHL (childLL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHL (childLL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childHL (childLL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childHL (childLL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childHL (childLL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childHL (childLL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011220022 :
    adaptiveCoverCheck 9 (childHL (childHL (childLL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL (childLL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childHL (childLL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL (childLL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childHL (childLL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL (childLL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childHL (childLL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL (childLL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHL (childLL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL (childLL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011220023 :
    adaptiveCoverCheck 9 (childHH (childHL (childLL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL (childLL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childHL (childLL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL (childLL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childHL (childLL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL (childLL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childHL (childLL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL (childLL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHL (childLL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL (childLL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011220030 :
    adaptiveCoverCheck 9 (childLL (childHH (childLL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH (childLL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childHH (childLL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHH (childLL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childHH (childLL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHH (childLL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childHH (childLL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childHH (childLL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childHH (childLL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childHH (childLL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011220031 :
    adaptiveCoverCheck 9 (childLH (childHH (childLL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH (childLL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childHH (childLL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHH (childLL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childHH (childLL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHH (childLL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childHH (childLL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childHH (childLL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childHH (childLL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childHH (childLL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011220032 :
    adaptiveCoverCheck 9 (childHL (childHH (childLL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH (childLL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childHH (childLL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH (childLL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childHH (childLL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH (childLL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childHH (childLL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH (childLL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHH (childLL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH (childLL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011220033 :
    adaptiveCoverCheck 9 (childHH (childHH (childLL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH (childLL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childHH (childLL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH (childLL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childHH (childLL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH (childLL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childHH (childLL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH (childLL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHH (childLL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH (childLL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011220120 :
    adaptiveCoverCheck 9 (childLL (childHL (childLH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL (childLH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childHL (childLH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHL (childLH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childHL (childLH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHL (childLH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childHL (childLH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childHL (childLH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childHL (childLH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childHL (childLH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011220121 :
    adaptiveCoverCheck 9 (childLH (childHL (childLH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL (childLH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childHL (childLH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHL (childLH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childHL (childLH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHL (childLH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childHL (childLH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childHL (childLH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childHL (childLH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childHL (childLH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011220122 :
    adaptiveCoverCheck 9 (childHL (childHL (childLH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL (childLH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childHL (childLH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL (childLH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childHL (childLH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL (childLH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childHL (childLH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL (childLH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHL (childLH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL (childLH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011220123 :
    adaptiveCoverCheck 9 (childHH (childHL (childLH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL (childLH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childHL (childLH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL (childLH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childHL (childLH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL (childLH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childHL (childLH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL (childLH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHL (childLH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL (childLH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011220130 :
    adaptiveCoverCheck 9 (childLL (childHH (childLH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH (childLH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childHH (childLH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHH (childLH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childHH (childLH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHH (childLH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childHH (childLH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childHH (childLH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childHH (childLH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childHH (childLH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011220131 :
    adaptiveCoverCheck 9 (childLH (childHH (childLH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH (childLH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childHH (childLH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHH (childLH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childHH (childLH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHH (childLH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childHH (childLH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childHH (childLH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childHH (childLH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childHH (childLH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011220132 :
    adaptiveCoverCheck 9 (childHL (childHH (childLH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH (childLH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childHH (childLH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH (childLH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childHH (childLH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH (childLH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childHH (childLH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH (childLH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHH (childLH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH (childLH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011220133 :
    adaptiveCoverCheck 9 (childHH (childHH (childLH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH (childLH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childHH (childLH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH (childLH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childHH (childLH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH (childLH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childHH (childLH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH (childLH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHH (childLH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH (childLH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011220200 :
    adaptiveCoverCheck 9 (childLL (childLL (childHL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLL (childHL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childLL (childHL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLL (childHL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childLL (childHL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLL (childHL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childLL (childHL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLL (childHL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childLL (childHL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLL (childHL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011220201 :
    adaptiveCoverCheck 9 (childLH (childLL (childHL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLL (childHL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childLL (childHL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLL (childHL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childLL (childHL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLL (childHL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childLL (childHL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLL (childHL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childLL (childHL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLL (childHL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011220210 :
    adaptiveCoverCheck 9 (childLL (childLH (childHL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLH (childHL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childLH (childHL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLH (childHL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childLH (childHL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLH (childHL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childLH (childHL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLH (childHL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childLH (childHL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLH (childHL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011220211 :
    adaptiveCoverCheck 9 (childLH (childLH (childHL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLH (childHL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childLH (childHL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLH (childHL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childLH (childHL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLH (childHL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childLH (childHL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLH (childHL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childLH (childHL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLH (childHL (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011220300 :
    adaptiveCoverCheck 9 (childLL (childLL (childHH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLL (childHH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childLL (childHH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLL (childHH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childLL (childHH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLL (childHH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childLL (childHH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLL (childHH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childLL (childHH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLL (childHH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011220301 :
    adaptiveCoverCheck 9 (childLH (childLL (childHH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLL (childHH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childLL (childHH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLL (childHH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childLL (childHH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLL (childHH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childLL (childHH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLL (childHH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childLL (childHH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLL (childHH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011220310 :
    adaptiveCoverCheck 9 (childLL (childLH (childHH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLH (childHH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childLH (childHH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLH (childHH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childLH (childHH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLH (childHH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childLH (childHH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLH (childHH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childLH (childHH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLH (childHH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011220311 :
    adaptiveCoverCheck 9 (childLH (childLH (childHH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLH (childHH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childLH (childHH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLH (childHH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childLH (childHH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLH (childHH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childLH (childHH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLH (childHH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childLH (childHH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLH (childHH (childLL (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011221020 :
    adaptiveCoverCheck 9 (childLL (childHL (childLL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL (childLL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childHL (childLL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHL (childLL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childHL (childLL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHL (childLL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childHL (childLL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childHL (childLL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childHL (childLL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childHL (childLL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011221021 :
    adaptiveCoverCheck 9 (childLH (childHL (childLL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL (childLL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childHL (childLL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHL (childLL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childHL (childLL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHL (childLL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childHL (childLL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childHL (childLL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childHL (childLL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childHL (childLL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011221022 :
    adaptiveCoverCheck 9 (childHL (childHL (childLL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL (childLL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childHL (childLL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL (childLL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childHL (childLL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL (childLL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childHL (childLL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL (childLL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHL (childLL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL (childLL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011221023 :
    adaptiveCoverCheck 9 (childHH (childHL (childLL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL (childLL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childHL (childLL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL (childLL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childHL (childLL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL (childLL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childHL (childLL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL (childLL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHL (childLL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL (childLL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011221030 :
    adaptiveCoverCheck 9 (childLL (childHH (childLL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH (childLL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childHH (childLL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHH (childLL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childHH (childLL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHH (childLL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childHH (childLL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childHH (childLL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childHH (childLL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childHH (childLL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011221031 :
    adaptiveCoverCheck 9 (childLH (childHH (childLL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH (childLL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childHH (childLL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHH (childLL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childHH (childLL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHH (childLL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childHH (childLL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childHH (childLL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childHH (childLL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childHH (childLL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011221032 :
    adaptiveCoverCheck 9 (childHL (childHH (childLL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH (childLL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childHH (childLL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH (childLL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childHH (childLL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH (childLL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childHH (childLL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH (childLL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHH (childLL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH (childLL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011221033 :
    adaptiveCoverCheck 9 (childHH (childHH (childLL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH (childLL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childHH (childLL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH (childLL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childHH (childLL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH (childLL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childHH (childLL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH (childLL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHH (childLL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH (childLL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011221120 :
    adaptiveCoverCheck 9 (childLL (childHL (childLH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL (childLH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childHL (childLH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHL (childLH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childHL (childLH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHL (childLH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childHL (childLH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childHL (childLH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childHL (childLH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childHL (childLH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011221121 :
    adaptiveCoverCheck 9 (childLH (childHL (childLH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL (childLH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childHL (childLH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHL (childLH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childHL (childLH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHL (childLH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childHL (childLH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childHL (childLH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childHL (childLH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childHL (childLH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011221122 :
    adaptiveCoverCheck 9 (childHL (childHL (childLH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL (childLH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childHL (childLH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL (childLH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childHL (childLH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL (childLH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childHL (childLH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL (childLH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHL (childLH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL (childLH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011221123 :
    adaptiveCoverCheck 9 (childHH (childHL (childLH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL (childLH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childHL (childLH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL (childLH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childHL (childLH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL (childLH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childHL (childLH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL (childLH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHL (childLH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL (childLH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011221130 :
    adaptiveCoverCheck 9 (childLL (childHH (childLH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH (childLH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childHH (childLH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHH (childLH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childHH (childLH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHH (childLH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childHH (childLH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childHH (childLH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childHH (childLH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childHH (childLH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011221131 :
    adaptiveCoverCheck 9 (childLH (childHH (childLH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH (childLH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childHH (childLH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHH (childLH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childHH (childLH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHH (childLH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childHH (childLH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childHH (childLH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childHH (childLH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childHH (childLH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011221132 :
    adaptiveCoverCheck 9 (childHL (childHH (childLH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH (childLH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childHH (childLH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH (childLH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childHH (childLH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH (childLH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childHH (childLH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH (childLH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHH (childLH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH (childLH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011221133 :
    adaptiveCoverCheck 9 (childHH (childHH (childLH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH (childLH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childHH (childLH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH (childLH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childHH (childLH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH (childLH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childHH (childLH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH (childLH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHH (childLH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH (childLH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011221200 :
    adaptiveCoverCheck 9 (childLL (childLL (childHL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLL (childHL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childLL (childHL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLL (childHL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childLL (childHL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLL (childHL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childLL (childHL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLL (childHL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childLL (childHL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLL (childHL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011221201 :
    adaptiveCoverCheck 9 (childLH (childLL (childHL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLL (childHL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childLL (childHL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLL (childHL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childLL (childHL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLL (childHL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childLL (childHL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLL (childHL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childLL (childHL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLL (childHL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011221210 :
    adaptiveCoverCheck 9 (childLL (childLH (childHL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLH (childHL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childLH (childHL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLH (childHL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childLH (childHL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLH (childHL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childLH (childHL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLH (childHL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childLH (childHL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLH (childHL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011221211 :
    adaptiveCoverCheck 9 (childLH (childLH (childHL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLH (childHL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childLH (childHL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLH (childHL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childLH (childHL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLH (childHL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childLH (childHL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLH (childHL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childLH (childHL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLH (childHL (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011221300 :
    adaptiveCoverCheck 9 (childLL (childLL (childHH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLL (childHH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childLL (childHH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLL (childHH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childLL (childHH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLL (childHH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childLL (childHH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLL (childHH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childLL (childHH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLL (childHH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011221301 :
    adaptiveCoverCheck 9 (childLH (childLL (childHH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLL (childHH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childLL (childHH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLL (childHH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childLL (childHH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLL (childHH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childLL (childHH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLL (childHH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childLL (childHH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLL (childHH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011221310 :
    adaptiveCoverCheck 9 (childLL (childLH (childHH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLH (childHH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childLH (childHH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLH (childHH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childLH (childHH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLH (childHH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childLH (childHH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLH (childHH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childLH (childHH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLH (childHH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011221311 :
    adaptiveCoverCheck 9 (childLH (childLH (childHH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLH (childHH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childLH (childHH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLH (childHH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childLH (childHH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLH (childHH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childLH (childHH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLH (childHH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childLH (childHH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLH (childHH (childLH (childHL (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011230020 :
    adaptiveCoverCheck 9 (childLL (childHL (childLL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL (childLL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childHL (childLL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHL (childLL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childHL (childLL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHL (childLL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childHL (childLL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childHL (childLL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childHL (childLL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childHL (childLL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011230021 :
    adaptiveCoverCheck 9 (childLH (childHL (childLL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL (childLL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childHL (childLL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHL (childLL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childHL (childLL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHL (childLL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childHL (childLL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childHL (childLL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childHL (childLL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childHL (childLL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011230022 :
    adaptiveCoverCheck 9 (childHL (childHL (childLL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL (childLL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childHL (childLL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL (childLL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childHL (childLL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL (childLL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childHL (childLL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL (childLL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHL (childLL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL (childLL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011230023 :
    adaptiveCoverCheck 9 (childHH (childHL (childLL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL (childLL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childHL (childLL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL (childLL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childHL (childLL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL (childLL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childHL (childLL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL (childLL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHL (childLL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL (childLL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011230030 :
    adaptiveCoverCheck 9 (childLL (childHH (childLL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH (childLL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childHH (childLL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHH (childLL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childHH (childLL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHH (childLL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childHH (childLL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childHH (childLL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childHH (childLL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childHH (childLL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011230031 :
    adaptiveCoverCheck 9 (childLH (childHH (childLL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH (childLL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childHH (childLL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHH (childLL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childHH (childLL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHH (childLL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childHH (childLL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childHH (childLL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childHH (childLL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childHH (childLL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011230032 :
    adaptiveCoverCheck 9 (childHL (childHH (childLL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH (childLL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childHH (childLL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH (childLL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childHH (childLL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH (childLL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childHH (childLL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH (childLL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHH (childLL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH (childLL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011230033 :
    adaptiveCoverCheck 9 (childHH (childHH (childLL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH (childLL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childHH (childLL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH (childLL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childHH (childLL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH (childLL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childHH (childLL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH (childLL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHH (childLL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH (childLL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011230120 :
    adaptiveCoverCheck 9 (childLL (childHL (childLH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL (childLH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childHL (childLH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHL (childLH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childHL (childLH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHL (childLH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childHL (childLH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childHL (childLH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childHL (childLH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childHL (childLH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011230121 :
    adaptiveCoverCheck 9 (childLH (childHL (childLH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL (childLH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childHL (childLH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHL (childLH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childHL (childLH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHL (childLH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childHL (childLH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childHL (childLH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childHL (childLH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childHL (childLH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011230122 :
    adaptiveCoverCheck 9 (childHL (childHL (childLH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL (childLH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childHL (childLH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL (childLH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childHL (childLH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL (childLH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childHL (childLH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL (childLH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHL (childLH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL (childLH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011230123 :
    adaptiveCoverCheck 9 (childHH (childHL (childLH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL (childLH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childHL (childLH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL (childLH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childHL (childLH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL (childLH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childHL (childLH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL (childLH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHL (childLH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL (childLH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011230130 :
    adaptiveCoverCheck 9 (childLL (childHH (childLH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH (childLH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childHH (childLH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHH (childLH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childHH (childLH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHH (childLH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childHH (childLH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childHH (childLH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childHH (childLH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childHH (childLH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011230131 :
    adaptiveCoverCheck 9 (childLH (childHH (childLH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH (childLH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childHH (childLH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHH (childLH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childHH (childLH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHH (childLH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childHH (childLH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childHH (childLH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childHH (childLH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childHH (childLH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011230132 :
    adaptiveCoverCheck 9 (childHL (childHH (childLH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH (childLH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childHH (childLH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH (childLH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childHH (childLH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH (childLH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childHH (childLH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH (childLH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHH (childLH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH (childLH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011230133 :
    adaptiveCoverCheck 9 (childHH (childHH (childLH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH (childLH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childHH (childLH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH (childLH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childHH (childLH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH (childLH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childHH (childLH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH (childLH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHH (childLH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH (childLH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011230200 :
    adaptiveCoverCheck 9 (childLL (childLL (childHL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLL (childHL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childLL (childHL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLL (childHL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childLL (childHL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLL (childHL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childLL (childHL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLL (childHL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childLL (childHL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLL (childHL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011230201 :
    adaptiveCoverCheck 9 (childLH (childLL (childHL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLL (childHL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childLL (childHL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLL (childHL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childLL (childHL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLL (childHL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childLL (childHL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLL (childHL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childLL (childHL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLL (childHL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011230210 :
    adaptiveCoverCheck 9 (childLL (childLH (childHL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLH (childHL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childLH (childHL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLH (childHL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childLH (childHL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLH (childHL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childLH (childHL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLH (childHL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childLH (childHL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLH (childHL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011230211 :
    adaptiveCoverCheck 9 (childLH (childLH (childHL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLH (childHL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childLH (childHL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLH (childHL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childLH (childHL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLH (childHL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childLH (childHL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLH (childHL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childLH (childHL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLH (childHL (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011230300 :
    adaptiveCoverCheck 9 (childLL (childLL (childHH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLL (childHH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childLL (childHH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLL (childHH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childLL (childHH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLL (childHH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childLL (childHH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLL (childHH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childLL (childHH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLL (childHH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011230301 :
    adaptiveCoverCheck 9 (childLH (childLL (childHH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLL (childHH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childLL (childHH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLL (childHH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childLL (childHH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLL (childHH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childLL (childHH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLL (childHH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childLL (childHH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLL (childHH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011230310 :
    adaptiveCoverCheck 9 (childLL (childLH (childHH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLH (childHH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childLH (childHH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLH (childHH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childLH (childHH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLH (childHH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childLH (childHH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLH (childHH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childLH (childHH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLH (childHH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011230311 :
    adaptiveCoverCheck 9 (childLH (childLH (childHH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLH (childHH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childLH (childHH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLH (childHH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childLH (childHH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLH (childHH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childLH (childHH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLH (childHH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childLH (childHH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLH (childHH (childLL (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011231020 :
    adaptiveCoverCheck 9 (childLL (childHL (childLL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL (childLL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childHL (childLL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHL (childLL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childHL (childLL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHL (childLL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childHL (childLL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childHL (childLL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childHL (childLL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childHL (childLL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011231021 :
    adaptiveCoverCheck 9 (childLH (childHL (childLL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL (childLL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childHL (childLL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHL (childLL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childHL (childLL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHL (childLL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childHL (childLL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childHL (childLL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childHL (childLL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childHL (childLL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011231022 :
    adaptiveCoverCheck 9 (childHL (childHL (childLL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL (childLL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childHL (childLL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL (childLL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childHL (childLL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL (childLL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childHL (childLL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL (childLL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHL (childLL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL (childLL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011231023 :
    adaptiveCoverCheck 9 (childHH (childHL (childLL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL (childLL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childHL (childLL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL (childLL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childHL (childLL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL (childLL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childHL (childLL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL (childLL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHL (childLL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL (childLL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011231030 :
    adaptiveCoverCheck 9 (childLL (childHH (childLL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH (childLL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childHH (childLL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHH (childLL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childHH (childLL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHH (childLL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childHH (childLL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childHH (childLL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childHH (childLL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childHH (childLL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011231031 :
    adaptiveCoverCheck 9 (childLH (childHH (childLL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH (childLL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childHH (childLL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHH (childLL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childHH (childLL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHH (childLL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childHH (childLL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childHH (childLL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childHH (childLL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childHH (childLL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011231032 :
    adaptiveCoverCheck 9 (childHL (childHH (childLL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH (childLL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childHH (childLL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH (childLL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childHH (childLL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH (childLL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childHH (childLL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH (childLL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHH (childLL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH (childLL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011231033 :
    adaptiveCoverCheck 9 (childHH (childHH (childLL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH (childLL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childHH (childLL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH (childLL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childHH (childLL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH (childLL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childHH (childLL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH (childLL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHH (childLL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH (childLL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011231120 :
    adaptiveCoverCheck 9 (childLL (childHL (childLH (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL (childLH (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childHL (childLH (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHL (childLH (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childHL (childLH (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHL (childLH (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childHL (childLH (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childHL (childLH (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childHL (childLH (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childHL (childLH (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011231122 :
    adaptiveCoverCheck 9 (childHL (childHL (childLH (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL (childLH (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childHL (childLH (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL (childLH (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childHL (childLH (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL (childLH (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childHL (childLH (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL (childLH (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHL (childLH (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL (childLH (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011231123 :
    adaptiveCoverCheck 9 (childHH (childHL (childLH (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL (childLH (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childHL (childLH (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL (childLH (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childHL (childLH (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL (childLH (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childHL (childLH (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL (childLH (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHL (childLH (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL (childLH (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011231132 :
    adaptiveCoverCheck 9 (childHL (childHH (childLH (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH (childLH (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childHH (childLH (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH (childLH (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childHH (childLH (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH (childLH (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childHH (childLH (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH (childLH (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHH (childLH (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH (childLH (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011231133 :
    adaptiveCoverCheck 9 (childHH (childHH (childLH (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH (childLH (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childHH (childLH (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH (childLH (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childHH (childLH (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH (childLH (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childHH (childLH (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH (childLH (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHH (childLH (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH (childLH (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011231200 :
    adaptiveCoverCheck 9 (childLL (childLL (childHL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLL (childHL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childLL (childHL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLL (childHL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childLL (childHL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLL (childHL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childLL (childHL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLL (childHL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childLL (childHL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLL (childHL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011231201 :
    adaptiveCoverCheck 9 (childLH (childLL (childHL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLL (childHL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childLL (childHL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLL (childHL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childLL (childHL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLL (childHL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childLL (childHL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLL (childHL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childLL (childHL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLL (childHL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011231210 :
    adaptiveCoverCheck 9 (childLL (childLH (childHL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLH (childHL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childLH (childHL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLH (childHL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childLH (childHL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLH (childHL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childLH (childHL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLH (childHL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childLH (childHL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLH (childHL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011231211 :
    adaptiveCoverCheck 9 (childLH (childLH (childHL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLH (childHL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childLH (childHL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLH (childHL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childLH (childHL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLH (childHL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childLH (childHL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLH (childHL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childLH (childHL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLH (childHL (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011231300 :
    adaptiveCoverCheck 9 (childLL (childLL (childHH (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLL (childHH (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childLL (childHH (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLL (childHH (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childLL (childHH (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLL (childHH (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childLL (childHH (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLL (childHH (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childLL (childHH (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLL (childHH (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011231301 :
    adaptiveCoverCheck 9 (childLH (childLL (childHH (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLL (childHH (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childLL (childHH (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLL (childHH (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childLL (childHH (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLL (childHH (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childLL (childHH (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLL (childHH (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childLL (childHH (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLL (childHH (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011231310 :
    adaptiveCoverCheck 9 (childLL (childLH (childHH (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLH (childHH (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childLH (childHH (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLH (childHH (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childLH (childHH (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLH (childHH (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childLH (childHH (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLH (childHH (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childLH (childHH (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLH (childHH (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011231311 :
    adaptiveCoverCheck 9 (childLH (childLH (childHH (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLH (childHH (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childLH (childHH (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLH (childHH (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childLH (childHH (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLH (childHH (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childLH (childHH (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLH (childHH (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childLH (childHH (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLH (childHH (childLH (childHH (childHL (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011320022 :
    adaptiveCoverCheck 9 (childHL (childHL (childLL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL (childLL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childHL (childLL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL (childLL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childHL (childLL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL (childLL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childHL (childLL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL (childLL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHL (childLL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL (childLL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011320023 :
    adaptiveCoverCheck 9 (childHH (childHL (childLL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL (childLL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childHL (childLL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL (childLL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childHL (childLL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL (childLL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childHL (childLL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL (childLL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHL (childLL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL (childLL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011320032 :
    adaptiveCoverCheck 9 (childHL (childHH (childLL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH (childLL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childHH (childLL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH (childLL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childHH (childLL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH (childLL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childHH (childLL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH (childLL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHH (childLL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH (childLL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011320033 :
    adaptiveCoverCheck 9 (childHH (childHH (childLL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH (childLL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childHH (childLL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH (childLL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childHH (childLL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH (childLL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childHH (childLL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH (childLL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHH (childLL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH (childLL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011320122 :
    adaptiveCoverCheck 9 (childHL (childHL (childLH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL (childLH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childHL (childLH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL (childLH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childHL (childLH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL (childLH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childHL (childLH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL (childLH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHL (childLH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL (childLH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011320123 :
    adaptiveCoverCheck 9 (childHH (childHL (childLH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL (childLH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childHL (childLH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL (childLH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childHL (childLH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL (childLH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childHL (childLH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL (childLH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHL (childLH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL (childLH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011320132 :
    adaptiveCoverCheck 9 (childHL (childHH (childLH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH (childLH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childHH (childLH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH (childLH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childHH (childLH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH (childLH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childHH (childLH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH (childLH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHH (childLH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH (childLH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011320133 :
    adaptiveCoverCheck 9 (childHH (childHH (childLH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH (childLH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childHH (childLH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH (childLH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childHH (childLH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH (childLH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childHH (childLH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH (childLH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHH (childLH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH (childLH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011320200 :
    adaptiveCoverCheck 9 (childLL (childLL (childHL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLL (childHL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childLL (childHL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLL (childHL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childLL (childHL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLL (childHL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childLL (childHL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLL (childHL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childLL (childHL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLL (childHL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011320201 :
    adaptiveCoverCheck 9 (childLH (childLL (childHL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLL (childHL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childLL (childHL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLL (childHL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childLL (childHL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLL (childHL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childLL (childHL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLL (childHL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childLL (childHL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLL (childHL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011320210 :
    adaptiveCoverCheck 9 (childLL (childLH (childHL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLH (childHL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childLH (childHL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLH (childHL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childLH (childHL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLH (childHL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childLH (childHL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLH (childHL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childLH (childHL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLH (childHL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011320211 :
    adaptiveCoverCheck 9 (childLH (childLH (childHL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLH (childHL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childLH (childHL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLH (childHL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childLH (childHL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLH (childHL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childLH (childHL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLH (childHL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childLH (childHL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLH (childHL (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011320300 :
    adaptiveCoverCheck 9 (childLL (childLL (childHH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLL (childHH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childLL (childHH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLL (childHH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childLL (childHH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLL (childHH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childLL (childHH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLL (childHH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childLL (childHH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLL (childHH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011320301 :
    adaptiveCoverCheck 9 (childLH (childLL (childHH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLL (childHH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childLL (childHH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLL (childHH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childLL (childHH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLL (childHH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childLL (childHH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLL (childHH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childLL (childHH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLL (childHH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011320310 :
    adaptiveCoverCheck 9 (childLL (childLH (childHH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLH (childHH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childLH (childHH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLH (childHH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childLH (childHH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLH (childHH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childLH (childHH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLH (childHH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childLH (childHH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLH (childHH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011320311 :
    adaptiveCoverCheck 9 (childLH (childLH (childHH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLH (childHH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childLH (childHH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLH (childHH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childLH (childHH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLH (childHH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childLH (childHH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLH (childHH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childLH (childHH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLH (childHH (childLL (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011321022 :
    adaptiveCoverCheck 9 (childHL (childHL (childLL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL (childLL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childHL (childLL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL (childLL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childHL (childLL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL (childLL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childHL (childLL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL (childLL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHL (childLL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL (childLL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011321023 :
    adaptiveCoverCheck 9 (childHH (childHL (childLL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL (childLL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childHL (childLL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL (childLL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childHL (childLL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL (childLL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childHL (childLL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL (childLL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHL (childLL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL (childLL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011321032 :
    adaptiveCoverCheck 9 (childHL (childHH (childLL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH (childLL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childHH (childLL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH (childLL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childHH (childLL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH (childLL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childHH (childLL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH (childLL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHH (childLL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH (childLL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011321033 :
    adaptiveCoverCheck 9 (childHH (childHH (childLL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH (childLL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childHH (childLL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH (childLL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childHH (childLL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH (childLL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childHH (childLL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH (childLL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHH (childLL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH (childLL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011321122 :
    adaptiveCoverCheck 9 (childHL (childHL (childLH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL (childLH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childHL (childLH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL (childLH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childHL (childLH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL (childLH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childHL (childLH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL (childLH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHL (childLH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL (childLH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011321123 :
    adaptiveCoverCheck 9 (childHH (childHL (childLH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL (childLH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childHL (childLH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL (childLH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childHL (childLH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL (childLH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childHL (childLH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL (childLH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHL (childLH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL (childLH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011321132 :
    adaptiveCoverCheck 9 (childHL (childHH (childLH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH (childLH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childHH (childLH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH (childLH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childHH (childLH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH (childLH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childHH (childLH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH (childLH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHH (childLH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH (childLH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011321133 :
    adaptiveCoverCheck 9 (childHH (childHH (childLH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH (childLH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childHH (childLH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH (childLH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childHH (childLH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH (childLH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childHH (childLH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH (childLH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHH (childLH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH (childLH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011321200 :
    adaptiveCoverCheck 9 (childLL (childLL (childHL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLL (childHL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childLL (childHL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLL (childHL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childLL (childHL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLL (childHL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childLL (childHL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLL (childHL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childLL (childHL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLL (childHL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011321201 :
    adaptiveCoverCheck 9 (childLH (childLL (childHL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLL (childHL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childLL (childHL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLL (childHL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childLL (childHL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLL (childHL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childLL (childHL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLL (childHL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childLL (childHL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLL (childHL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011321210 :
    adaptiveCoverCheck 9 (childLL (childLH (childHL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLH (childHL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childLH (childHL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLH (childHL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childLH (childHL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLH (childHL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childLH (childHL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLH (childHL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childLH (childHL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLH (childHL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011321211 :
    adaptiveCoverCheck 9 (childLH (childLH (childHL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLH (childHL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childLH (childHL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLH (childHL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childLH (childHL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLH (childHL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childLH (childHL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLH (childHL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childLH (childHL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLH (childHL (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011321300 :
    adaptiveCoverCheck 9 (childLL (childLL (childHH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLL (childHH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childLL (childHH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLL (childHH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childLL (childHH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLL (childHH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childLL (childHH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLL (childHH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childLL (childHH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLL (childHH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011321301 :
    adaptiveCoverCheck 9 (childLH (childLL (childHH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLL (childHH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childLL (childHH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLL (childHH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childLL (childHH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLL (childHH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childLL (childHH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLL (childHH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childLL (childHH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLL (childHH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011321310 :
    adaptiveCoverCheck 9 (childLL (childLH (childHH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLH (childHH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childLH (childHH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLH (childHH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childLH (childHH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLH (childHH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childLH (childHH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLH (childHH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childLH (childHH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLH (childHH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011321311 :
    adaptiveCoverCheck 9 (childLH (childLH (childHH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLH (childHH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childLH (childHH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLH (childHH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childLH (childHH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLH (childHH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childLH (childHH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLH (childHH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childLH (childHH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLH (childHH (childLH (childHL (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011330022 :
    adaptiveCoverCheck 9 (childHL (childHL (childLL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL (childLL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childHL (childLL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL (childLL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childHL (childLL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL (childLL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childHL (childLL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL (childLL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHL (childLL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL (childLL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011330023 :
    adaptiveCoverCheck 9 (childHH (childHL (childLL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL (childLL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childHL (childLL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL (childLL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childHL (childLL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL (childLL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childHL (childLL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL (childLL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHL (childLL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL (childLL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011330032 :
    adaptiveCoverCheck 9 (childHL (childHH (childLL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH (childLL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childHH (childLL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH (childLL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childHH (childLL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH (childLL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childHH (childLL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH (childLL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHH (childLL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH (childLL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011330033 :
    adaptiveCoverCheck 9 (childHH (childHH (childLL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH (childLL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childHH (childLL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH (childLL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childHH (childLL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH (childLL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childHH (childLL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH (childLL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHH (childLL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH (childLL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011330122 :
    adaptiveCoverCheck 9 (childHL (childHL (childLH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL (childLH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childHL (childLH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL (childLH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childHL (childLH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL (childLH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childHL (childLH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL (childLH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHL (childLH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL (childLH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011330123 :
    adaptiveCoverCheck 9 (childHH (childHL (childLH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL (childLH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childHL (childLH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL (childLH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childHL (childLH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL (childLH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childHL (childLH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL (childLH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHL (childLH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL (childLH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011330132 :
    adaptiveCoverCheck 9 (childHL (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHL (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHL (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHL (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHL (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011330133 :
    adaptiveCoverCheck 9 (childHH (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childHH (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childHH (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childHH (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childHH (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH (childLH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011330200 :
    adaptiveCoverCheck 9 (childLL (childLL (childHL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLL (childHL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childLL (childHL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLL (childHL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childLL (childHL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLL (childHL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childLL (childHL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLL (childHL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childLL (childHL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLL (childHL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011330201 :
    adaptiveCoverCheck 9 (childLH (childLL (childHL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLL (childHL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childLL (childHL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLL (childHL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childLL (childHL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLL (childHL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childLL (childHL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLL (childHL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childLL (childHL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLL (childHL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011330210 :
    adaptiveCoverCheck 9 (childLL (childLH (childHL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLH (childHL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childLH (childHL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLH (childHL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childLH (childHL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLH (childHL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childLH (childHL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLH (childHL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childLH (childHL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLH (childHL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011330211 :
    adaptiveCoverCheck 9 (childLH (childLH (childHL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLH (childHL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childLH (childHL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLH (childHL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childLH (childHL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLH (childHL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childLH (childHL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLH (childHL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childLH (childHL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLH (childHL (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011330300 :
    adaptiveCoverCheck 9 (childLL (childLL (childHH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLL (childHH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childLL (childHH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLL (childHH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childLL (childHH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLL (childHH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childLL (childHH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLL (childHH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childLL (childHH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLL (childHH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011330301 :
    adaptiveCoverCheck 9 (childLH (childLL (childHH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLL (childHH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childLL (childHH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLL (childHH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childLL (childHH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLL (childHH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childLL (childHH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLL (childHH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childLL (childHH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLL (childHH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011330310 :
    adaptiveCoverCheck 9 (childLL (childLH (childHH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLH (childHH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLL (childLH (childHH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLH (childHH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLL (childLH (childHH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLH (childHH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLL (childLH (childHH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLH (childHH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLL (childLH (childHH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLH (childHH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem e24KC2ThetaAboveLeaf0011330311 :
    adaptiveCoverCheck 9 (childLH (childLH (childHH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLH (childHH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))
    (by
      have h : ((childLL (childLH (childLH (childHH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLH (childHH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childLH (childLH (childLH (childHH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLH (childHH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHL (childLH (childLH (childHH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLH (childHH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)
    (by
      have h : ((childHH (childLH (childLH (childHH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot)))))))))))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLH (childHH (childLL (childHH (childHH (childLH (childLH (childLL (childLL e24ThetaAboveRoot))))))))))) h)

end PartE
end GerverSofa
