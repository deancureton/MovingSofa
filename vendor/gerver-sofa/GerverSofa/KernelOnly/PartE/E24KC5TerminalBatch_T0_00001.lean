import GerverSofa.KernelOnly.PartE.E24KC2ProofHelpers

/-! E24KC5 checkpoint-aware kernel batch. -/
noncomputable section

namespace GerverSofa
namespace PartE

theorem e24KC2PhiAboveLeaf00000 :
    adaptiveCoverCheck 11 (childLL (childLL (childLL (childLL (childLL e24PhiAboveRoot))))) = true := by
  have h : physicallyIrrelevant (childLL (childLL (childLL (childLL (childLL e24PhiAboveRoot))))) = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_physicallyIrrelevant 11 (childLL (childLL (childLL (childLL (childLL e24PhiAboveRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf00001 :
    adaptiveCoverCheck 11 (childLH (childLL (childLL (childLL (childLL e24PhiAboveRoot))))) = true := by
  have h : ((childLH (childLL (childLL (childLL (childLL e24PhiAboveRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLL (childLL (childLL (childLL e24PhiAboveRoot))))) h

theorem e24KC2PhiAboveLeaf00002 :
    adaptiveCoverCheck 11 (childHL (childLL (childLL (childLL (childLL e24PhiAboveRoot))))) = true := by
  have h : physicallyIrrelevant (childHL (childLL (childLL (childLL (childLL e24PhiAboveRoot))))) = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_physicallyIrrelevant 11 (childHL (childLL (childLL (childLL (childLL e24PhiAboveRoot))))) h

theorem e24KC2PhiAboveLeaf00003 :
    adaptiveCoverCheck 11 (childHH (childLL (childLL (childLL (childLL e24PhiAboveRoot))))) = true := by
  have h : physicallyIrrelevant (childHH (childLL (childLL (childLL (childLL e24PhiAboveRoot))))) = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_physicallyIrrelevant 11 (childHH (childLL (childLL (childLL (childLL e24PhiAboveRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf00010 :
    adaptiveCoverCheck 11 (childLL (childLH (childLL (childLL (childLL e24PhiAboveRoot))))) = true := by
  have h : ((childLL (childLH (childLL (childLL (childLL e24PhiAboveRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLH (childLL (childLL (childLL e24PhiAboveRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf00011 :
    adaptiveCoverCheck 11 (childLH (childLH (childLL (childLL (childLL e24PhiAboveRoot))))) = true := by
  have h : ((childLH (childLH (childLL (childLL (childLL e24PhiAboveRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLH (childLL (childLL (childLL e24PhiAboveRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf00012 :
    adaptiveCoverCheck 11 (childHL (childLH (childLL (childLL (childLL e24PhiAboveRoot))))) = true := by
  have h : ((childHL (childLH (childLL (childLL (childLL e24PhiAboveRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childLH (childLL (childLL (childLL e24PhiAboveRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf00013 :
    adaptiveCoverCheck 11 (childHH (childLH (childLL (childLL (childLL e24PhiAboveRoot))))) = true := by
  have h : ((childHH (childLH (childLL (childLL (childLL e24PhiAboveRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childLH (childLL (childLL (childLL e24PhiAboveRoot))))) h

theorem e24KC2PhiAboveLeaf0002 :
    adaptiveCoverCheck 12 (childHL (childLL (childLL (childLL e24PhiAboveRoot)))) = true := by
  have h : physicallyIrrelevant (childHL (childLL (childLL (childLL e24PhiAboveRoot)))) = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_physicallyIrrelevant 12 (childHL (childLL (childLL (childLL e24PhiAboveRoot)))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf0003 :
    adaptiveCoverCheck 12 (childHH (childLL (childLL (childLL e24PhiAboveRoot)))) = true := by
  have h : ((childHH (childLL (childLL (childLL e24PhiAboveRoot))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL (childLL (childLL e24PhiAboveRoot)))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf00100 :
    adaptiveCoverCheck 11 (childLL (childLL (childLH (childLL (childLL e24PhiAboveRoot))))) = true := by
  have h : ((childLL (childLL (childLH (childLL (childLL e24PhiAboveRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLL (childLH (childLL (childLL e24PhiAboveRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf00101 :
    adaptiveCoverCheck 11 (childLH (childLL (childLH (childLL (childLL e24PhiAboveRoot))))) = true := by
  have h : ((childLH (childLL (childLH (childLL (childLL e24PhiAboveRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLL (childLH (childLL (childLL e24PhiAboveRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf00102 :
    adaptiveCoverCheck 11 (childHL (childLL (childLH (childLL (childLL e24PhiAboveRoot))))) = true := by
  have h : ((childHL (childLL (childLH (childLL (childLL e24PhiAboveRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childLL (childLH (childLL (childLL e24PhiAboveRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf00103 :
    adaptiveCoverCheck 11 (childHH (childLL (childLH (childLL (childLL e24PhiAboveRoot))))) = true := by
  have h : ((childHH (childLL (childLH (childLL (childLL e24PhiAboveRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childLL (childLH (childLL (childLL e24PhiAboveRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf00110 :
    adaptiveCoverCheck 11 (childLL (childLH (childLH (childLL (childLL e24PhiAboveRoot))))) = true := by
  have h : ((childLL (childLH (childLH (childLL (childLL e24PhiAboveRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLH (childLH (childLL (childLL e24PhiAboveRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf00111 :
    adaptiveCoverCheck 11 (childLH (childLH (childLH (childLL (childLL e24PhiAboveRoot))))) = true := by
  have h : ((childLH (childLH (childLH (childLL (childLL e24PhiAboveRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLH (childLH (childLL (childLL e24PhiAboveRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf00112 :
    adaptiveCoverCheck 11 (childHL (childLH (childLH (childLL (childLL e24PhiAboveRoot))))) = true := by
  have h : ((childHL (childLH (childLH (childLL (childLL e24PhiAboveRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childLH (childLH (childLL (childLL e24PhiAboveRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf00113 :
    adaptiveCoverCheck 11 (childHH (childLH (childLH (childLL (childLL e24PhiAboveRoot))))) = true := by
  have h : ((childHH (childLH (childLH (childLL (childLL e24PhiAboveRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childLH (childLH (childLL (childLL e24PhiAboveRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf0012 :
    adaptiveCoverCheck 12 (childHL (childLH (childLL (childLL e24PhiAboveRoot)))) = true := by
  have h : ((childHL (childLH (childLL (childLL e24PhiAboveRoot))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childLL (childLL e24PhiAboveRoot)))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf0013 :
    adaptiveCoverCheck 12 (childHH (childLH (childLL (childLL e24PhiAboveRoot)))) = true := by
  have h : ((childHH (childLH (childLL (childLL e24PhiAboveRoot))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childLL (childLL e24PhiAboveRoot)))) h

theorem e24KC2PhiAboveLeaf002 :
    adaptiveCoverCheck 13 (childHL (childLL (childLL e24PhiAboveRoot))) = true := by
  have h : physicallyIrrelevant (childHL (childLL (childLL e24PhiAboveRoot))) = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_physicallyIrrelevant 13 (childHL (childLL (childLL e24PhiAboveRoot))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf0030 :
    adaptiveCoverCheck 12 (childLL (childHH (childLL (childLL e24PhiAboveRoot)))) = true := by
  have h : ((childLL (childHH (childLL (childLL e24PhiAboveRoot))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childHH (childLL (childLL e24PhiAboveRoot)))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf0031 :
    adaptiveCoverCheck 12 (childLH (childHH (childLL (childLL e24PhiAboveRoot)))) = true := by
  have h : ((childLH (childHH (childLL (childLL e24PhiAboveRoot))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childHH (childLL (childLL e24PhiAboveRoot)))) h

theorem e24KC2PhiAboveLeaf0032 :
    adaptiveCoverCheck 12 (childHL (childHH (childLL (childLL e24PhiAboveRoot)))) = true := by
  have h : physicallyIrrelevant (childHL (childHH (childLL (childLL e24PhiAboveRoot)))) = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_physicallyIrrelevant 12 (childHL (childHH (childLL (childLL e24PhiAboveRoot)))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf0033 :
    adaptiveCoverCheck 12 (childHH (childHH (childLL (childLL e24PhiAboveRoot)))) = true := by
  have h : ((childHH (childHH (childLL (childLL e24PhiAboveRoot))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childHH (childLL (childLL e24PhiAboveRoot)))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf01000 :
    adaptiveCoverCheck 11 (childLL (childLL (childLL (childLH (childLL e24PhiAboveRoot))))) = true := by
  have h : ((childLL (childLL (childLL (childLH (childLL e24PhiAboveRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLL (childLL (childLH (childLL e24PhiAboveRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf01001 :
    adaptiveCoverCheck 11 (childLH (childLL (childLL (childLH (childLL e24PhiAboveRoot))))) = true := by
  have h : ((childLH (childLL (childLL (childLH (childLL e24PhiAboveRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLL (childLL (childLH (childLL e24PhiAboveRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf01002 :
    adaptiveCoverCheck 11 (childHL (childLL (childLL (childLH (childLL e24PhiAboveRoot))))) = true := by
  have h : ((childHL (childLL (childLL (childLH (childLL e24PhiAboveRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childLL (childLL (childLH (childLL e24PhiAboveRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf01003 :
    adaptiveCoverCheck 11 (childHH (childLL (childLL (childLH (childLL e24PhiAboveRoot))))) = true := by
  have h : ((childHH (childLL (childLL (childLH (childLL e24PhiAboveRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childLL (childLL (childLH (childLL e24PhiAboveRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf01010 :
    adaptiveCoverCheck 11 (childLL (childLH (childLL (childLH (childLL e24PhiAboveRoot))))) = true := by
  have h : ((childLL (childLH (childLL (childLH (childLL e24PhiAboveRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLH (childLL (childLH (childLL e24PhiAboveRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf010110 :
    adaptiveCoverCheck 10 (childLL (childLH (childLH (childLL (childLH (childLL e24PhiAboveRoot)))))) = true := by
  have h : ((childLL (childLH (childLH (childLL (childLH (childLL e24PhiAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childLH (childLL (childLH (childLL e24PhiAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf010111 :
    adaptiveCoverCheck 10 (childLH (childLH (childLH (childLL (childLH (childLL e24PhiAboveRoot)))))) = true := by
  have h : ((childLH (childLH (childLH (childLL (childLH (childLL e24PhiAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childLH (childLL (childLH (childLL e24PhiAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf010112 :
    adaptiveCoverCheck 10 (childHL (childLH (childLH (childLL (childLH (childLL e24PhiAboveRoot)))))) = true := by
  have h : ((childHL (childLH (childLH (childLL (childLH (childLL e24PhiAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childLH (childLL (childLH (childLL e24PhiAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf010113 :
    adaptiveCoverCheck 10 (childHH (childLH (childLH (childLL (childLH (childLL e24PhiAboveRoot)))))) = true := by
  have h : ((childHH (childLH (childLH (childLL (childLH (childLL e24PhiAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childLH (childLL (childLH (childLL e24PhiAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf01012 :
    adaptiveCoverCheck 11 (childHL (childLH (childLL (childLH (childLL e24PhiAboveRoot))))) = true := by
  have h : ((childHL (childLH (childLL (childLH (childLL e24PhiAboveRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childLH (childLL (childLH (childLL e24PhiAboveRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf01013 :
    adaptiveCoverCheck 11 (childHH (childLH (childLL (childLH (childLL e24PhiAboveRoot))))) = true := by
  have h : ((childHH (childLH (childLL (childLH (childLL e24PhiAboveRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childLH (childLL (childLH (childLL e24PhiAboveRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf0102 :
    adaptiveCoverCheck 12 (childHL (childLL (childLH (childLL e24PhiAboveRoot)))) = true := by
  have h : ((childHL (childLL (childLH (childLL e24PhiAboveRoot))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL (childLH (childLL e24PhiAboveRoot)))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf0103 :
    adaptiveCoverCheck 12 (childHH (childLL (childLH (childLL e24PhiAboveRoot)))) = true := by
  have h : ((childHH (childLL (childLH (childLL e24PhiAboveRoot))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL (childLH (childLL e24PhiAboveRoot)))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf011000 :
    adaptiveCoverCheck 10 (childLL (childLL (childLL (childLH (childLH (childLL e24PhiAboveRoot)))))) = true := by
  have h : ((childLL (childLL (childLL (childLH (childLH (childLL e24PhiAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childLL (childLH (childLH (childLL e24PhiAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf011001 :
    adaptiveCoverCheck 10 (childLH (childLL (childLL (childLH (childLH (childLL e24PhiAboveRoot)))))) = true := by
  have h : ((childLH (childLL (childLL (childLH (childLH (childLL e24PhiAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childLL (childLH (childLH (childLL e24PhiAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf011002 :
    adaptiveCoverCheck 10 (childHL (childLL (childLL (childLH (childLH (childLL e24PhiAboveRoot)))))) = true := by
  have h : ((childHL (childLL (childLL (childLH (childLH (childLL e24PhiAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childLL (childLH (childLH (childLL e24PhiAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf011003 :
    adaptiveCoverCheck 10 (childHH (childLL (childLL (childLH (childLH (childLL e24PhiAboveRoot)))))) = true := by
  have h : ((childHH (childLL (childLL (childLH (childLH (childLL e24PhiAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childLL (childLH (childLH (childLL e24PhiAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf011010 :
    adaptiveCoverCheck 10 (childLL (childLH (childLL (childLH (childLH (childLL e24PhiAboveRoot)))))) = true := by
  have h : ((childLL (childLH (childLL (childLH (childLH (childLL e24PhiAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childLL (childLH (childLH (childLL e24PhiAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf011011 :
    adaptiveCoverCheck 10 (childLH (childLH (childLL (childLH (childLH (childLL e24PhiAboveRoot)))))) = true := by
  have h : ((childLH (childLH (childLL (childLH (childLH (childLL e24PhiAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childLL (childLH (childLH (childLL e24PhiAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf011012 :
    adaptiveCoverCheck 10 (childHL (childLH (childLL (childLH (childLH (childLL e24PhiAboveRoot)))))) = true := by
  have h : ((childHL (childLH (childLL (childLH (childLH (childLL e24PhiAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childLL (childLH (childLH (childLL e24PhiAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf011013 :
    adaptiveCoverCheck 10 (childHH (childLH (childLL (childLH (childLH (childLL e24PhiAboveRoot)))))) = true := by
  have h : ((childHH (childLH (childLL (childLH (childLH (childLL e24PhiAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childLL (childLH (childLH (childLL e24PhiAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf01102 :
    adaptiveCoverCheck 11 (childHL (childLL (childLH (childLH (childLL e24PhiAboveRoot))))) = true := by
  have h : ((childHL (childLL (childLH (childLH (childLL e24PhiAboveRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childLL (childLH (childLH (childLL e24PhiAboveRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf01103 :
    adaptiveCoverCheck 11 (childHH (childLL (childLH (childLH (childLL e24PhiAboveRoot))))) = true := by
  have h : ((childHH (childLL (childLH (childLH (childLL e24PhiAboveRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childLL (childLH (childLH (childLL e24PhiAboveRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf011100 :
    adaptiveCoverCheck 10 (childLL (childLL (childLH (childLH (childLH (childLL e24PhiAboveRoot)))))) = true := by
  have h : ((childLL (childLL (childLH (childLH (childLH (childLL e24PhiAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childLH (childLH (childLH (childLL e24PhiAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf011101 :
    adaptiveCoverCheck 10 (childLH (childLL (childLH (childLH (childLH (childLL e24PhiAboveRoot)))))) = true := by
  have h : ((childLH (childLL (childLH (childLH (childLH (childLL e24PhiAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childLH (childLH (childLH (childLL e24PhiAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf011102 :
    adaptiveCoverCheck 10 (childHL (childLL (childLH (childLH (childLH (childLL e24PhiAboveRoot)))))) = true := by
  have h : ((childHL (childLL (childLH (childLH (childLH (childLL e24PhiAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childLH (childLH (childLH (childLL e24PhiAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf011103 :
    adaptiveCoverCheck 10 (childHH (childLL (childLH (childLH (childLH (childLL e24PhiAboveRoot)))))) = true := by
  have h : ((childHH (childLL (childLH (childLH (childLH (childLL e24PhiAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childLH (childLH (childLH (childLL e24PhiAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf011110 :
    adaptiveCoverCheck 10 (childLL (childLH (childLH (childLH (childLH (childLL e24PhiAboveRoot)))))) = true := by
  have h : ((childLL (childLH (childLH (childLH (childLH (childLL e24PhiAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childLH (childLH (childLH (childLL e24PhiAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf011111 :
    adaptiveCoverCheck 10 (childLH (childLH (childLH (childLH (childLH (childLL e24PhiAboveRoot)))))) = true := by
  have h : ((childLH (childLH (childLH (childLH (childLH (childLL e24PhiAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childLH (childLH (childLH (childLL e24PhiAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf011112 :
    adaptiveCoverCheck 10 (childHL (childLH (childLH (childLH (childLH (childLL e24PhiAboveRoot)))))) = true := by
  have h : ((childHL (childLH (childLH (childLH (childLH (childLL e24PhiAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childLH (childLH (childLH (childLL e24PhiAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf011113 :
    adaptiveCoverCheck 10 (childHH (childLH (childLH (childLH (childLH (childLL e24PhiAboveRoot)))))) = true := by
  have h : ((childHH (childLH (childLH (childLH (childLH (childLL e24PhiAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childLH (childLH (childLH (childLL e24PhiAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf01112 :
    adaptiveCoverCheck 11 (childHL (childLH (childLH (childLH (childLL e24PhiAboveRoot))))) = true := by
  have h : ((childHL (childLH (childLH (childLH (childLL e24PhiAboveRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childLH (childLH (childLH (childLL e24PhiAboveRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf01113 :
    adaptiveCoverCheck 11 (childHH (childLH (childLH (childLH (childLL e24PhiAboveRoot))))) = true := by
  have h : ((childHH (childLH (childLH (childLH (childLL e24PhiAboveRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childLH (childLH (childLH (childLL e24PhiAboveRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf0112 :
    adaptiveCoverCheck 12 (childHL (childLH (childLH (childLL e24PhiAboveRoot)))) = true := by
  have h : ((childHL (childLH (childLH (childLL e24PhiAboveRoot))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childLH (childLL e24PhiAboveRoot)))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf0113 :
    adaptiveCoverCheck 12 (childHH (childLH (childLH (childLL e24PhiAboveRoot)))) = true := by
  have h : ((childHH (childLH (childLH (childLL e24PhiAboveRoot))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childLH (childLL e24PhiAboveRoot)))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf0120 :
    adaptiveCoverCheck 12 (childLL (childHL (childLH (childLL e24PhiAboveRoot)))) = true := by
  have h : ((childLL (childHL (childLH (childLL e24PhiAboveRoot))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childHL (childLH (childLL e24PhiAboveRoot)))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf0121 :
    adaptiveCoverCheck 12 (childLH (childHL (childLH (childLL e24PhiAboveRoot)))) = true := by
  have h : ((childLH (childHL (childLH (childLL e24PhiAboveRoot))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childHL (childLH (childLL e24PhiAboveRoot)))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf0122 :
    adaptiveCoverCheck 12 (childHL (childHL (childLH (childLL e24PhiAboveRoot)))) = true := by
  have h : ((childHL (childHL (childLH (childLL e24PhiAboveRoot))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childHL (childLH (childLL e24PhiAboveRoot)))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf0123 :
    adaptiveCoverCheck 12 (childHH (childHL (childLH (childLL e24PhiAboveRoot)))) = true := by
  have h : ((childHH (childHL (childLH (childLL e24PhiAboveRoot))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childHL (childLH (childLL e24PhiAboveRoot)))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf0130 :
    adaptiveCoverCheck 12 (childLL (childHH (childLH (childLL e24PhiAboveRoot)))) = true := by
  have h : ((childLL (childHH (childLH (childLL e24PhiAboveRoot))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childHH (childLH (childLL e24PhiAboveRoot)))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf0131 :
    adaptiveCoverCheck 12 (childLH (childHH (childLH (childLL e24PhiAboveRoot)))) = true := by
  have h : ((childLH (childHH (childLH (childLL e24PhiAboveRoot))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childHH (childLH (childLL e24PhiAboveRoot)))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf0132 :
    adaptiveCoverCheck 12 (childHL (childHH (childLH (childLL e24PhiAboveRoot)))) = true := by
  have h : ((childHL (childHH (childLH (childLL e24PhiAboveRoot))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childHH (childLH (childLL e24PhiAboveRoot)))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf0133 :
    adaptiveCoverCheck 12 (childHH (childHH (childLH (childLL e24PhiAboveRoot)))) = true := by
  have h : ((childHH (childHH (childLH (childLL e24PhiAboveRoot))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childHH (childLH (childLL e24PhiAboveRoot)))) h

theorem e24KC2PhiAboveLeaf02 :
    adaptiveCoverCheck 14 (childHL (childLL e24PhiAboveRoot)) = true := by
  have h : physicallyIrrelevant (childHL (childLL e24PhiAboveRoot)) = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_physicallyIrrelevant 14 (childHL (childLL e24PhiAboveRoot)) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf030 :
    adaptiveCoverCheck 13 (childLL (childHH (childLL e24PhiAboveRoot))) = true := by
  have h : ((childLL (childHH (childLL e24PhiAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL (childHH (childLL e24PhiAboveRoot))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf031 :
    adaptiveCoverCheck 13 (childLH (childHH (childLL e24PhiAboveRoot))) = true := by
  have h : ((childLH (childHH (childLL e24PhiAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH (childHH (childLL e24PhiAboveRoot))) h

theorem e24KC2PhiAboveLeaf032 :
    adaptiveCoverCheck 13 (childHL (childHH (childLL e24PhiAboveRoot))) = true := by
  have h : physicallyIrrelevant (childHL (childHH (childLL e24PhiAboveRoot))) = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_physicallyIrrelevant 13 (childHL (childHH (childLL e24PhiAboveRoot))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf033 :
    adaptiveCoverCheck 13 (childHH (childHH (childLL e24PhiAboveRoot))) = true := by
  have h : ((childHH (childHH (childLL e24PhiAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childHH (childLL e24PhiAboveRoot))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf100000 :
    adaptiveCoverCheck 10 (childLL (childLL (childLL (childLL (childLL (childLH e24PhiAboveRoot)))))) = true := by
  have h : ((childLL (childLL (childLL (childLL (childLL (childLH e24PhiAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childLL (childLL (childLL (childLH e24PhiAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf100001 :
    adaptiveCoverCheck 10 (childLH (childLL (childLL (childLL (childLL (childLH e24PhiAboveRoot)))))) = true := by
  have h : ((childLH (childLL (childLL (childLL (childLL (childLH e24PhiAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL (childLL (childLL (childLL (childLH e24PhiAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf100002 :
    adaptiveCoverCheck 10 (childHL (childLL (childLL (childLL (childLL (childLH e24PhiAboveRoot)))))) = true := by
  have h : ((childHL (childLL (childLL (childLL (childLL (childLH e24PhiAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childLL (childLL (childLL (childLH e24PhiAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf100003 :
    adaptiveCoverCheck 10 (childHH (childLL (childLL (childLL (childLL (childLH e24PhiAboveRoot)))))) = true := by
  have h : ((childHH (childLL (childLL (childLL (childLL (childLH e24PhiAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childLL (childLL (childLL (childLH e24PhiAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf100010 :
    adaptiveCoverCheck 10 (childLL (childLH (childLL (childLL (childLL (childLH e24PhiAboveRoot)))))) = true := by
  have h : ((childLL (childLH (childLL (childLL (childLL (childLH e24PhiAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH (childLL (childLL (childLL (childLH e24PhiAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf100011 :
    adaptiveCoverCheck 10 (childLH (childLH (childLL (childLL (childLL (childLH e24PhiAboveRoot)))))) = true := by
  have h : ((childLH (childLH (childLL (childLL (childLL (childLH e24PhiAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH (childLL (childLL (childLL (childLH e24PhiAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf100012 :
    adaptiveCoverCheck 10 (childHL (childLH (childLL (childLL (childLL (childLH e24PhiAboveRoot)))))) = true := by
  have h : ((childHL (childLH (childLL (childLL (childLL (childLH e24PhiAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childLL (childLL (childLL (childLH e24PhiAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf100013 :
    adaptiveCoverCheck 10 (childHH (childLH (childLL (childLL (childLL (childLH e24PhiAboveRoot)))))) = true := by
  have h : ((childHH (childLH (childLL (childLL (childLL (childLH e24PhiAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childLL (childLL (childLL (childLH e24PhiAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf10002 :
    adaptiveCoverCheck 11 (childHL (childLL (childLL (childLL (childLH e24PhiAboveRoot))))) = true := by
  have h : ((childHL (childLL (childLL (childLL (childLH e24PhiAboveRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childLL (childLL (childLL (childLH e24PhiAboveRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf10003 :
    adaptiveCoverCheck 11 (childHH (childLL (childLL (childLL (childLH e24PhiAboveRoot))))) = true := by
  have h : ((childHH (childLL (childLL (childLL (childLH e24PhiAboveRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childLL (childLL (childLL (childLH e24PhiAboveRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf100100 :
    adaptiveCoverCheck 10 (childLL (childLL (childLH (childLL (childLL (childLH e24PhiAboveRoot)))))) = true := by
  have h : ((childLL (childLL (childLH (childLL (childLL (childLH e24PhiAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL (childLH (childLL (childLL (childLH e24PhiAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1001010 :
    adaptiveCoverCheck 9 (childLL (childLH (childLL (childLH (childLL (childLL (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childLL (childLH (childLL (childLH (childLL (childLL (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childLL (childLH (childLL (childLL (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1001011 :
    adaptiveCoverCheck 9 (childLH (childLH (childLL (childLH (childLL (childLL (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childLH (childLH (childLL (childLH (childLL (childLL (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childLL (childLH (childLL (childLL (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1001012 :
    adaptiveCoverCheck 9 (childHL (childLH (childLL (childLH (childLL (childLL (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childHL (childLH (childLL (childLH (childLL (childLL (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childLL (childLH (childLL (childLL (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1001013 :
    adaptiveCoverCheck 9 (childHH (childLH (childLL (childLH (childLL (childLL (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childHH (childLH (childLL (childLH (childLL (childLL (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childLL (childLH (childLL (childLL (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf100102 :
    adaptiveCoverCheck 10 (childHL (childLL (childLH (childLL (childLL (childLH e24PhiAboveRoot)))))) = true := by
  have h : ((childHL (childLL (childLH (childLL (childLL (childLH e24PhiAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childLH (childLL (childLL (childLH e24PhiAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf100103 :
    adaptiveCoverCheck 10 (childHH (childLL (childLH (childLL (childLL (childLH e24PhiAboveRoot)))))) = true := by
  have h : ((childHH (childLL (childLH (childLL (childLL (childLH e24PhiAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childLH (childLL (childLL (childLH e24PhiAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1001100 :
    adaptiveCoverCheck 9 (childLL (childLL (childLH (childLH (childLL (childLL (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childLL (childLL (childLH (childLH (childLL (childLL (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childLH (childLH (childLL (childLL (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1001101 :
    adaptiveCoverCheck 9 (childLH (childLL (childLH (childLH (childLL (childLL (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childLH (childLL (childLH (childLH (childLL (childLL (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childLH (childLH (childLL (childLL (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1001102 :
    adaptiveCoverCheck 9 (childHL (childLL (childLH (childLH (childLL (childLL (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childHL (childLL (childLH (childLH (childLL (childLL (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childLH (childLH (childLL (childLL (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1001103 :
    adaptiveCoverCheck 9 (childHH (childLL (childLH (childLH (childLL (childLL (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childHH (childLL (childLH (childLH (childLL (childLL (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childLH (childLH (childLL (childLL (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1001110 :
    adaptiveCoverCheck 9 (childLL (childLH (childLH (childLH (childLL (childLL (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childLL (childLH (childLH (childLH (childLL (childLL (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childLH (childLH (childLL (childLL (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1001111 :
    adaptiveCoverCheck 9 (childLH (childLH (childLH (childLH (childLL (childLL (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childLH (childLH (childLH (childLH (childLL (childLL (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childLH (childLH (childLL (childLL (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1001112 :
    adaptiveCoverCheck 9 (childHL (childLH (childLH (childLH (childLL (childLL (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childHL (childLH (childLH (childLH (childLL (childLL (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childLH (childLH (childLL (childLL (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1001113 :
    adaptiveCoverCheck 9 (childHH (childLH (childLH (childLH (childLL (childLL (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childHH (childLH (childLH (childLH (childLL (childLL (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childLH (childLH (childLL (childLL (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf100112 :
    adaptiveCoverCheck 10 (childHL (childLH (childLH (childLL (childLL (childLH e24PhiAboveRoot)))))) = true := by
  have h : ((childHL (childLH (childLH (childLL (childLL (childLH e24PhiAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childLH (childLL (childLL (childLH e24PhiAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf100113 :
    adaptiveCoverCheck 10 (childHH (childLH (childLH (childLL (childLL (childLH e24PhiAboveRoot)))))) = true := by
  have h : ((childHH (childLH (childLH (childLL (childLL (childLH e24PhiAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childLH (childLL (childLL (childLH e24PhiAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf10012 :
    adaptiveCoverCheck 11 (childHL (childLH (childLL (childLL (childLH e24PhiAboveRoot))))) = true := by
  have h : ((childHL (childLH (childLL (childLL (childLH e24PhiAboveRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childLH (childLL (childLL (childLH e24PhiAboveRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf10013 :
    adaptiveCoverCheck 11 (childHH (childLH (childLL (childLL (childLH e24PhiAboveRoot))))) = true := by
  have h : ((childHH (childLH (childLL (childLL (childLH e24PhiAboveRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childLH (childLL (childLL (childLH e24PhiAboveRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf10020 :
    adaptiveCoverCheck 11 (childLL (childHL (childLL (childLL (childLH e24PhiAboveRoot))))) = true := by
  have h : ((childLL (childHL (childLL (childLL (childLH e24PhiAboveRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHL (childLL (childLL (childLH e24PhiAboveRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf10021 :
    adaptiveCoverCheck 11 (childLH (childHL (childLL (childLL (childLH e24PhiAboveRoot))))) = true := by
  have h : ((childLH (childHL (childLL (childLL (childLH e24PhiAboveRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHL (childLL (childLL (childLH e24PhiAboveRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf10022 :
    adaptiveCoverCheck 11 (childHL (childHL (childLL (childLL (childLH e24PhiAboveRoot))))) = true := by
  have h : ((childHL (childHL (childLL (childLL (childLH e24PhiAboveRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childLL (childLL (childLH e24PhiAboveRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf10023 :
    adaptiveCoverCheck 11 (childHH (childHL (childLL (childLL (childLH e24PhiAboveRoot))))) = true := by
  have h : ((childHH (childHL (childLL (childLL (childLH e24PhiAboveRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childLL (childLL (childLH e24PhiAboveRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf10030 :
    adaptiveCoverCheck 11 (childLL (childHH (childLL (childLL (childLH e24PhiAboveRoot))))) = true := by
  have h : ((childLL (childHH (childLL (childLL (childLH e24PhiAboveRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHH (childLL (childLL (childLH e24PhiAboveRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf10031 :
    adaptiveCoverCheck 11 (childLH (childHH (childLL (childLL (childLH e24PhiAboveRoot))))) = true := by
  have h : ((childLH (childHH (childLL (childLL (childLH e24PhiAboveRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHH (childLL (childLL (childLH e24PhiAboveRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf10032 :
    adaptiveCoverCheck 11 (childHL (childHH (childLL (childLL (childLH e24PhiAboveRoot))))) = true := by
  have h : ((childHL (childHH (childLL (childLL (childLH e24PhiAboveRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childLL (childLL (childLH e24PhiAboveRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf10033 :
    adaptiveCoverCheck 11 (childHH (childHH (childLL (childLL (childLH e24PhiAboveRoot))))) = true := by
  have h : ((childHH (childHH (childLL (childLL (childLH e24PhiAboveRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childLL (childLL (childLH e24PhiAboveRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1010000 :
    adaptiveCoverCheck 9 (childLL (childLL (childLL (childLL (childLH (childLL (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childLL (childLL (childLL (childLL (childLH (childLL (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childLL (childLL (childLH (childLL (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1010001 :
    adaptiveCoverCheck 9 (childLH (childLL (childLL (childLL (childLH (childLL (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childLH (childLL (childLL (childLL (childLH (childLL (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childLL (childLL (childLH (childLL (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1010002 :
    adaptiveCoverCheck 9 (childHL (childLL (childLL (childLL (childLH (childLL (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childHL (childLL (childLL (childLL (childLH (childLL (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childLL (childLL (childLH (childLL (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1010003 :
    adaptiveCoverCheck 9 (childHH (childLL (childLL (childLL (childLH (childLL (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childHH (childLL (childLL (childLL (childLH (childLL (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childLL (childLL (childLH (childLL (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1010010 :
    adaptiveCoverCheck 9 (childLL (childLH (childLL (childLL (childLH (childLL (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childLL (childLH (childLL (childLL (childLH (childLL (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childLL (childLL (childLH (childLL (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1010011 :
    adaptiveCoverCheck 9 (childLH (childLH (childLL (childLL (childLH (childLL (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childLH (childLH (childLL (childLL (childLH (childLL (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childLL (childLL (childLH (childLL (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1010012 :
    adaptiveCoverCheck 9 (childHL (childLH (childLL (childLL (childLH (childLL (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childHL (childLH (childLL (childLL (childLH (childLL (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childLL (childLL (childLH (childLL (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1010013 :
    adaptiveCoverCheck 9 (childHH (childLH (childLL (childLL (childLH (childLL (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childHH (childLH (childLL (childLL (childLH (childLL (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childLL (childLL (childLH (childLL (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf101002 :
    adaptiveCoverCheck 10 (childHL (childLL (childLL (childLH (childLL (childLH e24PhiAboveRoot)))))) = true := by
  have h : ((childHL (childLL (childLL (childLH (childLL (childLH e24PhiAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childLL (childLH (childLL (childLH e24PhiAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf101003 :
    adaptiveCoverCheck 10 (childHH (childLL (childLL (childLH (childLL (childLH e24PhiAboveRoot)))))) = true := by
  have h : ((childHH (childLL (childLL (childLH (childLL (childLH e24PhiAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childLL (childLH (childLL (childLH e24PhiAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1010100 :
    adaptiveCoverCheck 9 (childLL (childLL (childLH (childLL (childLH (childLL (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childLL (childLL (childLH (childLL (childLH (childLL (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childLH (childLL (childLH (childLL (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1010101 :
    adaptiveCoverCheck 9 (childLH (childLL (childLH (childLL (childLH (childLL (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childLH (childLL (childLH (childLL (childLH (childLL (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childLH (childLL (childLH (childLL (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1010102 :
    adaptiveCoverCheck 9 (childHL (childLL (childLH (childLL (childLH (childLL (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childHL (childLL (childLH (childLL (childLH (childLL (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childLH (childLL (childLH (childLL (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1010103 :
    adaptiveCoverCheck 9 (childHH (childLL (childLH (childLL (childLH (childLL (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childHH (childLL (childLH (childLL (childLH (childLL (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childLH (childLL (childLH (childLL (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1010110 :
    adaptiveCoverCheck 9 (childLL (childLH (childLH (childLL (childLH (childLL (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childLL (childLH (childLH (childLL (childLH (childLL (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childLH (childLL (childLH (childLL (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1010111 :
    adaptiveCoverCheck 9 (childLH (childLH (childLH (childLL (childLH (childLL (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childLH (childLH (childLH (childLL (childLH (childLL (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childLH (childLL (childLH (childLL (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1010112 :
    adaptiveCoverCheck 9 (childHL (childLH (childLH (childLL (childLH (childLL (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childHL (childLH (childLH (childLL (childLH (childLL (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childLH (childLL (childLH (childLL (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1010113 :
    adaptiveCoverCheck 9 (childHH (childLH (childLH (childLL (childLH (childLL (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childHH (childLH (childLH (childLL (childLH (childLL (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childLH (childLL (childLH (childLL (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf101012 :
    adaptiveCoverCheck 10 (childHL (childLH (childLL (childLH (childLL (childLH e24PhiAboveRoot)))))) = true := by
  have h : ((childHL (childLH (childLL (childLH (childLL (childLH e24PhiAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childLL (childLH (childLL (childLH e24PhiAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf101013 :
    adaptiveCoverCheck 10 (childHH (childLH (childLL (childLH (childLL (childLH e24PhiAboveRoot)))))) = true := by
  have h : ((childHH (childLH (childLL (childLH (childLL (childLH e24PhiAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childLL (childLH (childLL (childLH e24PhiAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf10102 :
    adaptiveCoverCheck 11 (childHL (childLL (childLH (childLL (childLH e24PhiAboveRoot))))) = true := by
  have h : ((childHL (childLL (childLH (childLL (childLH e24PhiAboveRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childLL (childLH (childLL (childLH e24PhiAboveRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf10103 :
    adaptiveCoverCheck 11 (childHH (childLL (childLH (childLL (childLH e24PhiAboveRoot))))) = true := by
  have h : ((childHH (childLL (childLH (childLL (childLH e24PhiAboveRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childLL (childLH (childLL (childLH e24PhiAboveRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1011000 :
    adaptiveCoverCheck 9 (childLL (childLL (childLL (childLH (childLH (childLL (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childLL (childLL (childLL (childLH (childLH (childLL (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childLL (childLH (childLH (childLL (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1011001 :
    adaptiveCoverCheck 9 (childLH (childLL (childLL (childLH (childLH (childLL (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childLH (childLL (childLL (childLH (childLH (childLL (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childLL (childLH (childLH (childLL (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1011002 :
    adaptiveCoverCheck 9 (childHL (childLL (childLL (childLH (childLH (childLL (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childHL (childLL (childLL (childLH (childLH (childLL (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childLL (childLH (childLH (childLL (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1011003 :
    adaptiveCoverCheck 9 (childHH (childLL (childLL (childLH (childLH (childLL (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childHH (childLL (childLL (childLH (childLH (childLL (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childLL (childLH (childLH (childLL (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1011010 :
    adaptiveCoverCheck 9 (childLL (childLH (childLL (childLH (childLH (childLL (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childLL (childLH (childLL (childLH (childLH (childLL (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childLL (childLH (childLH (childLL (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1011012 :
    adaptiveCoverCheck 9 (childHL (childLH (childLL (childLH (childLH (childLL (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childHL (childLH (childLL (childLH (childLH (childLL (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childLL (childLH (childLH (childLL (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1011013 :
    adaptiveCoverCheck 9 (childHH (childLH (childLL (childLH (childLH (childLL (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childHH (childLH (childLL (childLH (childLH (childLL (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childLL (childLH (childLH (childLL (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf101102 :
    adaptiveCoverCheck 10 (childHL (childLL (childLH (childLH (childLL (childLH e24PhiAboveRoot)))))) = true := by
  have h : ((childHL (childLL (childLH (childLH (childLL (childLH e24PhiAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childLH (childLH (childLL (childLH e24PhiAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf101103 :
    adaptiveCoverCheck 10 (childHH (childLL (childLH (childLH (childLL (childLH e24PhiAboveRoot)))))) = true := by
  have h : ((childHH (childLL (childLH (childLH (childLL (childLH e24PhiAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childLH (childLH (childLL (childLH e24PhiAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1011102 :
    adaptiveCoverCheck 9 (childHL (childLL (childLH (childLH (childLH (childLL (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childHL (childLL (childLH (childLH (childLH (childLL (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childLH (childLH (childLH (childLL (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1011103 :
    adaptiveCoverCheck 9 (childHH (childLL (childLH (childLH (childLH (childLL (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childHH (childLL (childLH (childLH (childLH (childLL (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childLH (childLH (childLH (childLL (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1011112 :
    adaptiveCoverCheck 9 (childHL (childLH (childLH (childLH (childLH (childLL (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childHL (childLH (childLH (childLH (childLH (childLL (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childLH (childLH (childLH (childLL (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1011113 :
    adaptiveCoverCheck 9 (childHH (childLH (childLH (childLH (childLH (childLL (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childHH (childLH (childLH (childLH (childLH (childLL (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childLH (childLH (childLH (childLL (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf101112 :
    adaptiveCoverCheck 10 (childHL (childLH (childLH (childLH (childLL (childLH e24PhiAboveRoot)))))) = true := by
  have h : ((childHL (childLH (childLH (childLH (childLL (childLH e24PhiAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childLH (childLH (childLL (childLH e24PhiAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf101113 :
    adaptiveCoverCheck 10 (childHH (childLH (childLH (childLH (childLL (childLH e24PhiAboveRoot)))))) = true := by
  have h : ((childHH (childLH (childLH (childLH (childLL (childLH e24PhiAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH (childLH (childLH (childLL (childLH e24PhiAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf10112 :
    adaptiveCoverCheck 11 (childHL (childLH (childLH (childLL (childLH e24PhiAboveRoot))))) = true := by
  have h : ((childHL (childLH (childLH (childLL (childLH e24PhiAboveRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childLH (childLH (childLL (childLH e24PhiAboveRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf101130 :
    adaptiveCoverCheck 10 (childLL (childHH (childLH (childLH (childLL (childLH e24PhiAboveRoot)))))) = true := by
  have h : ((childLL (childHH (childLH (childLH (childLL (childLH e24PhiAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHH (childLH (childLH (childLL (childLH e24PhiAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf101131 :
    adaptiveCoverCheck 10 (childLH (childHH (childLH (childLH (childLL (childLH e24PhiAboveRoot)))))) = true := by
  have h : ((childLH (childHH (childLH (childLH (childLL (childLH e24PhiAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHH (childLH (childLH (childLL (childLH e24PhiAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf101132 :
    adaptiveCoverCheck 10 (childHL (childHH (childLH (childLH (childLL (childLH e24PhiAboveRoot)))))) = true := by
  have h : ((childHL (childHH (childLH (childLH (childLL (childLH e24PhiAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childLH (childLH (childLL (childLH e24PhiAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf101133 :
    adaptiveCoverCheck 10 (childHH (childHH (childLH (childLH (childLL (childLH e24PhiAboveRoot)))))) = true := by
  have h : ((childHH (childHH (childLH (childLH (childLL (childLH e24PhiAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childLH (childLH (childLL (childLH e24PhiAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf10120 :
    adaptiveCoverCheck 11 (childLL (childHL (childLH (childLL (childLH e24PhiAboveRoot))))) = true := by
  have h : ((childLL (childHL (childLH (childLL (childLH e24PhiAboveRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHL (childLH (childLL (childLH e24PhiAboveRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf10121 :
    adaptiveCoverCheck 11 (childLH (childHL (childLH (childLL (childLH e24PhiAboveRoot))))) = true := by
  have h : ((childLH (childHL (childLH (childLL (childLH e24PhiAboveRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHL (childLH (childLL (childLH e24PhiAboveRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf10122 :
    adaptiveCoverCheck 11 (childHL (childHL (childLH (childLL (childLH e24PhiAboveRoot))))) = true := by
  have h : ((childHL (childHL (childLH (childLL (childLH e24PhiAboveRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childLH (childLL (childLH e24PhiAboveRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf10123 :
    adaptiveCoverCheck 11 (childHH (childHL (childLH (childLL (childLH e24PhiAboveRoot))))) = true := by
  have h : ((childHH (childHL (childLH (childLL (childLH e24PhiAboveRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childLH (childLL (childLH e24PhiAboveRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf10130 :
    adaptiveCoverCheck 11 (childLL (childHH (childLH (childLL (childLH e24PhiAboveRoot))))) = true := by
  have h : ((childLL (childHH (childLH (childLL (childLH e24PhiAboveRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHH (childLH (childLL (childLH e24PhiAboveRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf10131 :
    adaptiveCoverCheck 11 (childLH (childHH (childLH (childLL (childLH e24PhiAboveRoot))))) = true := by
  have h : ((childLH (childHH (childLH (childLL (childLH e24PhiAboveRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHH (childLH (childLL (childLH e24PhiAboveRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf10132 :
    adaptiveCoverCheck 11 (childHL (childHH (childLH (childLL (childLH e24PhiAboveRoot))))) = true := by
  have h : ((childHL (childHH (childLH (childLL (childLH e24PhiAboveRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childLH (childLL (childLH e24PhiAboveRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf10133 :
    adaptiveCoverCheck 11 (childHH (childHH (childLH (childLL (childLH e24PhiAboveRoot))))) = true := by
  have h : ((childHH (childHH (childLH (childLL (childLH e24PhiAboveRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childLH (childLL (childLH e24PhiAboveRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1020 :
    adaptiveCoverCheck 12 (childLL (childHL (childLL (childLH e24PhiAboveRoot)))) = true := by
  have h : ((childLL (childHL (childLL (childLH e24PhiAboveRoot))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childHL (childLL (childLH e24PhiAboveRoot)))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1021 :
    adaptiveCoverCheck 12 (childLH (childHL (childLL (childLH e24PhiAboveRoot)))) = true := by
  have h : ((childLH (childHL (childLL (childLH e24PhiAboveRoot))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childHL (childLL (childLH e24PhiAboveRoot)))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1022 :
    adaptiveCoverCheck 12 (childHL (childHL (childLL (childLH e24PhiAboveRoot)))) = true := by
  have h : ((childHL (childHL (childLL (childLH e24PhiAboveRoot))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childHL (childLL (childLH e24PhiAboveRoot)))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1023 :
    adaptiveCoverCheck 12 (childHH (childHL (childLL (childLH e24PhiAboveRoot)))) = true := by
  have h : ((childHH (childHL (childLL (childLH e24PhiAboveRoot))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childHL (childLL (childLH e24PhiAboveRoot)))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1030 :
    adaptiveCoverCheck 12 (childLL (childHH (childLL (childLH e24PhiAboveRoot)))) = true := by
  have h : ((childLL (childHH (childLL (childLH e24PhiAboveRoot))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childHH (childLL (childLH e24PhiAboveRoot)))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1031 :
    adaptiveCoverCheck 12 (childLH (childHH (childLL (childLH e24PhiAboveRoot)))) = true := by
  have h : ((childLH (childHH (childLL (childLH e24PhiAboveRoot))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childHH (childLL (childLH e24PhiAboveRoot)))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1032 :
    adaptiveCoverCheck 12 (childHL (childHH (childLL (childLH e24PhiAboveRoot)))) = true := by
  have h : ((childHL (childHH (childLL (childLH e24PhiAboveRoot))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childHH (childLL (childLH e24PhiAboveRoot)))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1033 :
    adaptiveCoverCheck 12 (childHH (childHH (childLL (childLH e24PhiAboveRoot)))) = true := by
  have h : ((childHH (childHH (childLL (childLH e24PhiAboveRoot))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childHH (childLL (childLH e24PhiAboveRoot)))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1100002 :
    adaptiveCoverCheck 9 (childHL (childLL (childLL (childLL (childLL (childLH (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childHL (childLL (childLL (childLL (childLL (childLH (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childLL (childLL (childLL (childLH (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1100003 :
    adaptiveCoverCheck 9 (childHH (childLL (childLL (childLL (childLL (childLH (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childHH (childLL (childLL (childLL (childLL (childLH (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childLL (childLL (childLL (childLH (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1100012 :
    adaptiveCoverCheck 9 (childHL (childLH (childLL (childLL (childLL (childLH (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childHL (childLH (childLL (childLL (childLL (childLH (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childLL (childLL (childLL (childLH (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1100013 :
    adaptiveCoverCheck 9 (childHH (childLH (childLL (childLL (childLL (childLH (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childHH (childLH (childLL (childLL (childLL (childLH (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childLL (childLL (childLL (childLH (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf110002 :
    adaptiveCoverCheck 10 (childHL (childLL (childLL (childLL (childLH (childLH e24PhiAboveRoot)))))) = true := by
  have h : ((childHL (childLL (childLL (childLL (childLH (childLH e24PhiAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL (childLL (childLL (childLH (childLH e24PhiAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf110003 :
    adaptiveCoverCheck 10 (childHH (childLL (childLL (childLL (childLH (childLH e24PhiAboveRoot)))))) = true := by
  have h : ((childHH (childLL (childLL (childLL (childLH (childLH e24PhiAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL (childLL (childLL (childLH (childLH e24PhiAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1100102 :
    adaptiveCoverCheck 9 (childHL (childLL (childLH (childLL (childLL (childLH (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childHL (childLL (childLH (childLL (childLL (childLH (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childLH (childLL (childLL (childLH (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1100103 :
    adaptiveCoverCheck 9 (childHH (childLL (childLH (childLL (childLL (childLH (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childHH (childLL (childLH (childLL (childLL (childLH (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childLH (childLL (childLL (childLH (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1100112 :
    adaptiveCoverCheck 9 (childHL (childLH (childLH (childLL (childLL (childLH (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childHL (childLH (childLH (childLL (childLL (childLH (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childLH (childLL (childLL (childLH (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1100113 :
    adaptiveCoverCheck 9 (childHH (childLH (childLH (childLL (childLL (childLH (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childHH (childLH (childLH (childLL (childLL (childLH (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childLH (childLL (childLL (childLH (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf110012 :
    adaptiveCoverCheck 10 (childHL (childLH (childLL (childLL (childLH (childLH e24PhiAboveRoot)))))) = true := by
  have h : ((childHL (childLH (childLL (childLL (childLH (childLH e24PhiAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH (childLL (childLL (childLH (childLH e24PhiAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1100130 :
    adaptiveCoverCheck 9 (childLL (childHH (childLH (childLL (childLL (childLH (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childLL (childHH (childLH (childLL (childLL (childLH (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childLH (childLL (childLL (childLH (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1100131 :
    adaptiveCoverCheck 9 (childLH (childHH (childLH (childLL (childLL (childLH (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childLH (childHH (childLH (childLL (childLL (childLH (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childLH (childLL (childLL (childLH (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1100132 :
    adaptiveCoverCheck 9 (childHL (childHH (childLH (childLL (childLL (childLH (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childHL (childHH (childLH (childLL (childLL (childLH (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childLH (childLL (childLL (childLH (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1100133 :
    adaptiveCoverCheck 9 (childHH (childHH (childLH (childLL (childLL (childLH (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childHH (childHH (childLH (childLL (childLL (childLH (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childLH (childLL (childLL (childLH (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf110020 :
    adaptiveCoverCheck 10 (childLL (childHL (childLL (childLL (childLH (childLH e24PhiAboveRoot)))))) = true := by
  have h : ((childLL (childHL (childLL (childLL (childLH (childLH e24PhiAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHL (childLL (childLL (childLH (childLH e24PhiAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf110021 :
    adaptiveCoverCheck 10 (childLH (childHL (childLL (childLL (childLH (childLH e24PhiAboveRoot)))))) = true := by
  have h : ((childLH (childHL (childLL (childLL (childLH (childLH e24PhiAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHL (childLL (childLL (childLH (childLH e24PhiAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf110022 :
    adaptiveCoverCheck 10 (childHL (childHL (childLL (childLL (childLH (childLH e24PhiAboveRoot)))))) = true := by
  have h : ((childHL (childHL (childLL (childLL (childLH (childLH e24PhiAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childLL (childLL (childLH (childLH e24PhiAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf110023 :
    adaptiveCoverCheck 10 (childHH (childHL (childLL (childLL (childLH (childLH e24PhiAboveRoot)))))) = true := by
  have h : ((childHH (childHL (childLL (childLL (childLH (childLH e24PhiAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childLL (childLL (childLH (childLH e24PhiAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf110030 :
    adaptiveCoverCheck 10 (childLL (childHH (childLL (childLL (childLH (childLH e24PhiAboveRoot)))))) = true := by
  have h : ((childLL (childHH (childLL (childLL (childLH (childLH e24PhiAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHH (childLL (childLL (childLH (childLH e24PhiAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf110031 :
    adaptiveCoverCheck 10 (childLH (childHH (childLL (childLL (childLH (childLH e24PhiAboveRoot)))))) = true := by
  have h : ((childLH (childHH (childLL (childLL (childLH (childLH e24PhiAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHH (childLL (childLL (childLH (childLH e24PhiAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf110032 :
    adaptiveCoverCheck 10 (childHL (childHH (childLL (childLL (childLH (childLH e24PhiAboveRoot)))))) = true := by
  have h : ((childHL (childHH (childLL (childLL (childLH (childLH e24PhiAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childLL (childLL (childLH (childLH e24PhiAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf110033 :
    adaptiveCoverCheck 10 (childHH (childHH (childLL (childLL (childLH (childLH e24PhiAboveRoot)))))) = true := by
  have h : ((childHH (childHH (childLL (childLL (childLH (childLH e24PhiAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childLL (childLL (childLH (childLH e24PhiAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1101002 :
    adaptiveCoverCheck 9 (childHL (childLL (childLL (childLH (childLL (childLH (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childHL (childLL (childLL (childLH (childLL (childLH (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childLL (childLH (childLL (childLH (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1101003 :
    adaptiveCoverCheck 9 (childHH (childLL (childLL (childLH (childLL (childLH (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childHH (childLL (childLL (childLH (childLL (childLH (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childLL (childLH (childLL (childLH (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1101020 :
    adaptiveCoverCheck 9 (childLL (childHL (childLL (childLH (childLL (childLH (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childLL (childHL (childLL (childLH (childLL (childLH (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childLL (childLH (childLL (childLH (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1101021 :
    adaptiveCoverCheck 9 (childLH (childHL (childLL (childLH (childLL (childLH (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childLH (childHL (childLL (childLH (childLL (childLH (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childLL (childLH (childLL (childLH (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1101022 :
    adaptiveCoverCheck 9 (childHL (childHL (childLL (childLH (childLL (childLH (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childHL (childHL (childLL (childLH (childLL (childLH (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childLL (childLH (childLL (childLH (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1101023 :
    adaptiveCoverCheck 9 (childHH (childHL (childLL (childLH (childLL (childLH (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childHH (childHL (childLL (childLH (childLL (childLH (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childLL (childLH (childLL (childLH (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1101030 :
    adaptiveCoverCheck 9 (childLL (childHH (childLL (childLH (childLL (childLH (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childLL (childHH (childLL (childLH (childLL (childLH (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childLL (childLH (childLL (childLH (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1101031 :
    adaptiveCoverCheck 9 (childLH (childHH (childLL (childLH (childLL (childLH (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childLH (childHH (childLL (childLH (childLL (childLH (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childLL (childLH (childLL (childLH (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1101032 :
    adaptiveCoverCheck 9 (childHL (childHH (childLL (childLH (childLL (childLH (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childHL (childHH (childLL (childLH (childLL (childLH (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childLL (childLH (childLL (childLH (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1101033 :
    adaptiveCoverCheck 9 (childHH (childHH (childLL (childLH (childLL (childLH (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childHH (childHH (childLL (childLH (childLL (childLH (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childLL (childLH (childLL (childLH (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1101120 :
    adaptiveCoverCheck 9 (childLL (childHL (childLH (childLH (childLL (childLH (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childLL (childHL (childLH (childLH (childLL (childLH (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childLH (childLH (childLL (childLH (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1101121 :
    adaptiveCoverCheck 9 (childLH (childHL (childLH (childLH (childLL (childLH (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childLH (childHL (childLH (childLH (childLL (childLH (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childLH (childLH (childLL (childLH (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1101122 :
    adaptiveCoverCheck 9 (childHL (childHL (childLH (childLH (childLL (childLH (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childHL (childHL (childLH (childLH (childLL (childLH (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childLH (childLH (childLL (childLH (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1101123 :
    adaptiveCoverCheck 9 (childHH (childHL (childLH (childLH (childLL (childLH (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childHH (childHL (childLH (childLH (childLL (childLH (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childLH (childLH (childLL (childLH (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1101130 :
    adaptiveCoverCheck 9 (childLL (childHH (childLH (childLH (childLL (childLH (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childLL (childHH (childLH (childLH (childLL (childLH (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childLH (childLH (childLL (childLH (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1101131 :
    adaptiveCoverCheck 9 (childLH (childHH (childLH (childLH (childLL (childLH (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childLH (childHH (childLH (childLH (childLL (childLH (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childLH (childLH (childLL (childLH (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1101132 :
    adaptiveCoverCheck 9 (childHL (childHH (childLH (childLH (childLL (childLH (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childHL (childHH (childLH (childLH (childLL (childLH (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childLH (childLH (childLL (childLH (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1101133 :
    adaptiveCoverCheck 9 (childHH (childHH (childLH (childLH (childLL (childLH (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childHH (childHH (childLH (childLH (childLL (childLH (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childLH (childLH (childLL (childLH (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf110120 :
    adaptiveCoverCheck 10 (childLL (childHL (childLH (childLL (childLH (childLH e24PhiAboveRoot)))))) = true := by
  have h : ((childLL (childHL (childLH (childLL (childLH (childLH e24PhiAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHL (childLH (childLL (childLH (childLH e24PhiAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf110121 :
    adaptiveCoverCheck 10 (childLH (childHL (childLH (childLL (childLH (childLH e24PhiAboveRoot)))))) = true := by
  have h : ((childLH (childHL (childLH (childLL (childLH (childLH e24PhiAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHL (childLH (childLL (childLH (childLH e24PhiAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf110122 :
    adaptiveCoverCheck 10 (childHL (childHL (childLH (childLL (childLH (childLH e24PhiAboveRoot)))))) = true := by
  have h : ((childHL (childHL (childLH (childLL (childLH (childLH e24PhiAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childLH (childLL (childLH (childLH e24PhiAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf110123 :
    adaptiveCoverCheck 10 (childHH (childHL (childLH (childLL (childLH (childLH e24PhiAboveRoot)))))) = true := by
  have h : ((childHH (childHL (childLH (childLL (childLH (childLH e24PhiAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childLH (childLL (childLH (childLH e24PhiAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf110130 :
    adaptiveCoverCheck 10 (childLL (childHH (childLH (childLL (childLH (childLH e24PhiAboveRoot)))))) = true := by
  have h : ((childLL (childHH (childLH (childLL (childLH (childLH e24PhiAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHH (childLH (childLL (childLH (childLH e24PhiAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf110131 :
    adaptiveCoverCheck 10 (childLH (childHH (childLH (childLL (childLH (childLH e24PhiAboveRoot)))))) = true := by
  have h : ((childLH (childHH (childLH (childLL (childLH (childLH e24PhiAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHH (childLH (childLL (childLH (childLH e24PhiAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf110132 :
    adaptiveCoverCheck 10 (childHL (childHH (childLH (childLL (childLH (childLH e24PhiAboveRoot)))))) = true := by
  have h : ((childHL (childHH (childLH (childLL (childLH (childLH e24PhiAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childLH (childLL (childLH (childLH e24PhiAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf110133 :
    adaptiveCoverCheck 10 (childHH (childHH (childLH (childLL (childLH (childLH e24PhiAboveRoot)))))) = true := by
  have h : ((childHH (childHH (childLH (childLL (childLH (childLH e24PhiAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childLH (childLL (childLH (childLH e24PhiAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf11020 :
    adaptiveCoverCheck 11 (childLL (childHL (childLL (childLH (childLH e24PhiAboveRoot))))) = true := by
  have h : ((childLL (childHL (childLL (childLH (childLH e24PhiAboveRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHL (childLL (childLH (childLH e24PhiAboveRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf11021 :
    adaptiveCoverCheck 11 (childLH (childHL (childLL (childLH (childLH e24PhiAboveRoot))))) = true := by
  have h : ((childLH (childHL (childLL (childLH (childLH e24PhiAboveRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHL (childLL (childLH (childLH e24PhiAboveRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf11022 :
    adaptiveCoverCheck 11 (childHL (childHL (childLL (childLH (childLH e24PhiAboveRoot))))) = true := by
  have h : ((childHL (childHL (childLL (childLH (childLH e24PhiAboveRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childLL (childLH (childLH e24PhiAboveRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf11023 :
    adaptiveCoverCheck 11 (childHH (childHL (childLL (childLH (childLH e24PhiAboveRoot))))) = true := by
  have h : ((childHH (childHL (childLL (childLH (childLH e24PhiAboveRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childLL (childLH (childLH e24PhiAboveRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf11030 :
    adaptiveCoverCheck 11 (childLL (childHH (childLL (childLH (childLH e24PhiAboveRoot))))) = true := by
  have h : ((childLL (childHH (childLL (childLH (childLH e24PhiAboveRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHH (childLL (childLH (childLH e24PhiAboveRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf11031 :
    adaptiveCoverCheck 11 (childLH (childHH (childLL (childLH (childLH e24PhiAboveRoot))))) = true := by
  have h : ((childLH (childHH (childLL (childLH (childLH e24PhiAboveRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHH (childLL (childLH (childLH e24PhiAboveRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf11032 :
    adaptiveCoverCheck 11 (childHL (childHH (childLL (childLH (childLH e24PhiAboveRoot))))) = true := by
  have h : ((childHL (childHH (childLL (childLH (childLH e24PhiAboveRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childLL (childLH (childLH e24PhiAboveRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf11033 :
    adaptiveCoverCheck 11 (childHH (childHH (childLL (childLH (childLH e24PhiAboveRoot))))) = true := by
  have h : ((childHH (childHH (childLL (childLH (childLH e24PhiAboveRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childLL (childLH (childLH e24PhiAboveRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1110020 :
    adaptiveCoverCheck 9 (childLL (childHL (childLL (childLL (childLH (childLH (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childLL (childHL (childLL (childLL (childLH (childLH (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childLL (childLL (childLH (childLH (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1110021 :
    adaptiveCoverCheck 9 (childLH (childHL (childLL (childLL (childLH (childLH (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childLH (childHL (childLL (childLL (childLH (childLH (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childLL (childLL (childLH (childLH (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1110022 :
    adaptiveCoverCheck 9 (childHL (childHL (childLL (childLL (childLH (childLH (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childHL (childHL (childLL (childLL (childLH (childLH (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childLL (childLL (childLH (childLH (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1110023 :
    adaptiveCoverCheck 9 (childHH (childHL (childLL (childLL (childLH (childLH (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childHH (childHL (childLL (childLL (childLH (childLH (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childLL (childLL (childLH (childLH (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1110030 :
    adaptiveCoverCheck 9 (childLL (childHH (childLL (childLL (childLH (childLH (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childLL (childHH (childLL (childLL (childLH (childLH (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childLL (childLL (childLH (childLH (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1110031 :
    adaptiveCoverCheck 9 (childLH (childHH (childLL (childLL (childLH (childLH (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childLH (childHH (childLL (childLL (childLH (childLH (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childLL (childLL (childLH (childLH (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1110032 :
    adaptiveCoverCheck 9 (childHL (childHH (childLL (childLL (childLH (childLH (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childHL (childHH (childLL (childLL (childLH (childLH (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childLL (childLL (childLH (childLH (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1110033 :
    adaptiveCoverCheck 9 (childHH (childHH (childLL (childLL (childLH (childLH (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childHH (childHH (childLL (childLL (childLH (childLH (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childLL (childLL (childLH (childLH (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1110120 :
    adaptiveCoverCheck 9 (childLL (childHL (childLH (childLL (childLH (childLH (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childLL (childHL (childLH (childLL (childLH (childLH (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childLH (childLL (childLH (childLH (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1110121 :
    adaptiveCoverCheck 9 (childLH (childHL (childLH (childLL (childLH (childLH (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childLH (childHL (childLH (childLL (childLH (childLH (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childLH (childLL (childLH (childLH (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1110122 :
    adaptiveCoverCheck 9 (childHL (childHL (childLH (childLL (childLH (childLH (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childHL (childHL (childLH (childLL (childLH (childLH (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childLH (childLL (childLH (childLH (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1110123 :
    adaptiveCoverCheck 9 (childHH (childHL (childLH (childLL (childLH (childLH (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childHH (childHL (childLH (childLL (childLH (childLH (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childLH (childLL (childLH (childLH (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1110130 :
    adaptiveCoverCheck 9 (childLL (childHH (childLH (childLL (childLH (childLH (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childLL (childHH (childLH (childLL (childLH (childLH (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childLH (childLL (childLH (childLH (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1110131 :
    adaptiveCoverCheck 9 (childLH (childHH (childLH (childLL (childLH (childLH (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childLH (childHH (childLH (childLL (childLH (childLH (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childLH (childLL (childLH (childLH (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1110132 :
    adaptiveCoverCheck 9 (childHL (childHH (childLH (childLL (childLH (childLH (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childHL (childHH (childLH (childLL (childLH (childLH (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childLH (childLL (childLH (childLH (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1110133 :
    adaptiveCoverCheck 9 (childHH (childHH (childLH (childLL (childLH (childLH (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childHH (childHH (childLH (childLL (childLH (childLH (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childLH (childLL (childLH (childLH (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf111020 :
    adaptiveCoverCheck 10 (childLL (childHL (childLL (childLH (childLH (childLH e24PhiAboveRoot)))))) = true := by
  have h : ((childLL (childHL (childLL (childLH (childLH (childLH e24PhiAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHL (childLL (childLH (childLH (childLH e24PhiAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf111021 :
    adaptiveCoverCheck 10 (childLH (childHL (childLL (childLH (childLH (childLH e24PhiAboveRoot)))))) = true := by
  have h : ((childLH (childHL (childLL (childLH (childLH (childLH e24PhiAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHL (childLL (childLH (childLH (childLH e24PhiAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf111022 :
    adaptiveCoverCheck 10 (childHL (childHL (childLL (childLH (childLH (childLH e24PhiAboveRoot)))))) = true := by
  have h : ((childHL (childHL (childLL (childLH (childLH (childLH e24PhiAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childLL (childLH (childLH (childLH e24PhiAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf111023 :
    adaptiveCoverCheck 10 (childHH (childHL (childLL (childLH (childLH (childLH e24PhiAboveRoot)))))) = true := by
  have h : ((childHH (childHL (childLL (childLH (childLH (childLH e24PhiAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childLL (childLH (childLH (childLH e24PhiAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf111030 :
    adaptiveCoverCheck 10 (childLL (childHH (childLL (childLH (childLH (childLH e24PhiAboveRoot)))))) = true := by
  have h : ((childLL (childHH (childLL (childLH (childLH (childLH e24PhiAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHH (childLL (childLH (childLH (childLH e24PhiAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf111031 :
    adaptiveCoverCheck 10 (childLH (childHH (childLL (childLH (childLH (childLH e24PhiAboveRoot)))))) = true := by
  have h : ((childLH (childHH (childLL (childLH (childLH (childLH e24PhiAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHH (childLL (childLH (childLH (childLH e24PhiAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf111032 :
    adaptiveCoverCheck 10 (childHL (childHH (childLL (childLH (childLH (childLH e24PhiAboveRoot)))))) = true := by
  have h : ((childHL (childHH (childLL (childLH (childLH (childLH e24PhiAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childLL (childLH (childLH (childLH e24PhiAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf111033 :
    adaptiveCoverCheck 10 (childHH (childHH (childLL (childLH (childLH (childLH e24PhiAboveRoot)))))) = true := by
  have h : ((childHH (childHH (childLL (childLH (childLH (childLH e24PhiAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childLL (childLH (childLH (childLH e24PhiAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1111020 :
    adaptiveCoverCheck 9 (childLL (childHL (childLL (childLH (childLH (childLH (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childLL (childHL (childLL (childLH (childLH (childLH (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childLL (childLH (childLH (childLH (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1111021 :
    adaptiveCoverCheck 9 (childLH (childHL (childLL (childLH (childLH (childLH (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childLH (childHL (childLL (childLH (childLH (childLH (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childLL (childLH (childLH (childLH (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1111022 :
    adaptiveCoverCheck 9 (childHL (childHL (childLL (childLH (childLH (childLH (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childHL (childHL (childLL (childLH (childLH (childLH (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childLL (childLH (childLH (childLH (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1111023 :
    adaptiveCoverCheck 9 (childHH (childHL (childLL (childLH (childLH (childLH (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childHH (childHL (childLL (childLH (childLH (childLH (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childLL (childLH (childLH (childLH (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1111030 :
    adaptiveCoverCheck 9 (childLL (childHH (childLL (childLH (childLH (childLH (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childLL (childHH (childLL (childLH (childLH (childLH (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childLL (childLH (childLH (childLH (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1111031 :
    adaptiveCoverCheck 9 (childLH (childHH (childLL (childLH (childLH (childLH (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childLH (childHH (childLL (childLH (childLH (childLH (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childLL (childLH (childLH (childLH (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1111032 :
    adaptiveCoverCheck 9 (childHL (childHH (childLL (childLH (childLH (childLH (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childHL (childHH (childLL (childLH (childLH (childLH (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childLL (childLH (childLH (childLH (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1111033 :
    adaptiveCoverCheck 9 (childHH (childHH (childLL (childLH (childLH (childLH (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childHH (childHH (childLL (childLH (childLH (childLH (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childLL (childLH (childLH (childLH (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1111120 :
    adaptiveCoverCheck 9 (childLL (childHL (childLH (childLH (childLH (childLH (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childLL (childHL (childLH (childLH (childLH (childLH (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childLH (childLH (childLH (childLH (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1111121 :
    adaptiveCoverCheck 9 (childLH (childHL (childLH (childLH (childLH (childLH (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childLH (childHL (childLH (childLH (childLH (childLH (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childLH (childLH (childLH (childLH (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1111122 :
    adaptiveCoverCheck 9 (childHL (childHL (childLH (childLH (childLH (childLH (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childHL (childHL (childLH (childLH (childLH (childLH (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childLH (childLH (childLH (childLH (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1111123 :
    adaptiveCoverCheck 9 (childHH (childHL (childLH (childLH (childLH (childLH (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childHH (childHL (childLH (childLH (childLH (childLH (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childLH (childLH (childLH (childLH (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1111130 :
    adaptiveCoverCheck 9 (childLL (childHH (childLH (childLH (childLH (childLH (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childLL (childHH (childLH (childLH (childLH (childLH (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childLH (childLH (childLH (childLH (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1111132 :
    adaptiveCoverCheck 9 (childHL (childHH (childLH (childLH (childLH (childLH (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childHL (childHH (childLH (childLH (childLH (childLH (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childLH (childLH (childLH (childLH (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1111133 :
    adaptiveCoverCheck 9 (childHH (childHH (childLH (childLH (childLH (childLH (childLH e24PhiAboveRoot))))))) = true := by
  have h : ((childHH (childHH (childLH (childLH (childLH (childLH (childLH e24PhiAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childLH (childLH (childLH (childLH (childLH e24PhiAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf111120 :
    adaptiveCoverCheck 10 (childLL (childHL (childLH (childLH (childLH (childLH e24PhiAboveRoot)))))) = true := by
  have h : ((childLL (childHL (childLH (childLH (childLH (childLH e24PhiAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHL (childLH (childLH (childLH (childLH e24PhiAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf111121 :
    adaptiveCoverCheck 10 (childLH (childHL (childLH (childLH (childLH (childLH e24PhiAboveRoot)))))) = true := by
  have h : ((childLH (childHL (childLH (childLH (childLH (childLH e24PhiAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHL (childLH (childLH (childLH (childLH e24PhiAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf111122 :
    adaptiveCoverCheck 10 (childHL (childHL (childLH (childLH (childLH (childLH e24PhiAboveRoot)))))) = true := by
  have h : ((childHL (childHL (childLH (childLH (childLH (childLH e24PhiAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childLH (childLH (childLH (childLH e24PhiAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf111123 :
    adaptiveCoverCheck 10 (childHH (childHL (childLH (childLH (childLH (childLH e24PhiAboveRoot)))))) = true := by
  have h : ((childHH (childHL (childLH (childLH (childLH (childLH e24PhiAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childLH (childLH (childLH (childLH e24PhiAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf111130 :
    adaptiveCoverCheck 10 (childLL (childHH (childLH (childLH (childLH (childLH e24PhiAboveRoot)))))) = true := by
  have h : ((childLL (childHH (childLH (childLH (childLH (childLH e24PhiAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHH (childLH (childLH (childLH (childLH e24PhiAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf111131 :
    adaptiveCoverCheck 10 (childLH (childHH (childLH (childLH (childLH (childLH e24PhiAboveRoot)))))) = true := by
  have h : ((childLH (childHH (childLH (childLH (childLH (childLH e24PhiAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHH (childLH (childLH (childLH (childLH e24PhiAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf111132 :
    adaptiveCoverCheck 10 (childHL (childHH (childLH (childLH (childLH (childLH e24PhiAboveRoot)))))) = true := by
  have h : ((childHL (childHH (childLH (childLH (childLH (childLH e24PhiAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childLH (childLH (childLH (childLH e24PhiAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf111133 :
    adaptiveCoverCheck 10 (childHH (childHH (childLH (childLH (childLH (childLH e24PhiAboveRoot)))))) = true := by
  have h : ((childHH (childHH (childLH (childLH (childLH (childLH e24PhiAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childLH (childLH (childLH (childLH e24PhiAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf11120 :
    adaptiveCoverCheck 11 (childLL (childHL (childLH (childLH (childLH e24PhiAboveRoot))))) = true := by
  have h : ((childLL (childHL (childLH (childLH (childLH e24PhiAboveRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHL (childLH (childLH (childLH e24PhiAboveRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf11121 :
    adaptiveCoverCheck 11 (childLH (childHL (childLH (childLH (childLH e24PhiAboveRoot))))) = true := by
  have h : ((childLH (childHL (childLH (childLH (childLH e24PhiAboveRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHL (childLH (childLH (childLH e24PhiAboveRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf11122 :
    adaptiveCoverCheck 11 (childHL (childHL (childLH (childLH (childLH e24PhiAboveRoot))))) = true := by
  have h : ((childHL (childHL (childLH (childLH (childLH e24PhiAboveRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childLH (childLH (childLH e24PhiAboveRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf11123 :
    adaptiveCoverCheck 11 (childHH (childHL (childLH (childLH (childLH e24PhiAboveRoot))))) = true := by
  have h : ((childHH (childHL (childLH (childLH (childLH e24PhiAboveRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childLH (childLH (childLH e24PhiAboveRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf11130 :
    adaptiveCoverCheck 11 (childLL (childHH (childLH (childLH (childLH e24PhiAboveRoot))))) = true := by
  have h : ((childLL (childHH (childLH (childLH (childLH e24PhiAboveRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHH (childLH (childLH (childLH e24PhiAboveRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf11131 :
    adaptiveCoverCheck 11 (childLH (childHH (childLH (childLH (childLH e24PhiAboveRoot))))) = true := by
  have h : ((childLH (childHH (childLH (childLH (childLH e24PhiAboveRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHH (childLH (childLH (childLH e24PhiAboveRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf11132 :
    adaptiveCoverCheck 11 (childHL (childHH (childLH (childLH (childLH e24PhiAboveRoot))))) = true := by
  have h : ((childHL (childHH (childLH (childLH (childLH e24PhiAboveRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childLH (childLH (childLH e24PhiAboveRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf11133 :
    adaptiveCoverCheck 11 (childHH (childHH (childLH (childLH (childLH e24PhiAboveRoot))))) = true := by
  have h : ((childHH (childHH (childLH (childLH (childLH e24PhiAboveRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childLH (childLH (childLH e24PhiAboveRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1120 :
    adaptiveCoverCheck 12 (childLL (childHL (childLH (childLH e24PhiAboveRoot)))) = true := by
  have h : ((childLL (childHL (childLH (childLH e24PhiAboveRoot))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childHL (childLH (childLH e24PhiAboveRoot)))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1121 :
    adaptiveCoverCheck 12 (childLH (childHL (childLH (childLH e24PhiAboveRoot)))) = true := by
  have h : ((childLH (childHL (childLH (childLH e24PhiAboveRoot))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childHL (childLH (childLH e24PhiAboveRoot)))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1122 :
    adaptiveCoverCheck 12 (childHL (childHL (childLH (childLH e24PhiAboveRoot)))) = true := by
  have h : ((childHL (childHL (childLH (childLH e24PhiAboveRoot))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childHL (childLH (childLH e24PhiAboveRoot)))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1123 :
    adaptiveCoverCheck 12 (childHH (childHL (childLH (childLH e24PhiAboveRoot)))) = true := by
  have h : ((childHH (childHL (childLH (childLH e24PhiAboveRoot))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childHL (childLH (childLH e24PhiAboveRoot)))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1130 :
    adaptiveCoverCheck 12 (childLL (childHH (childLH (childLH e24PhiAboveRoot)))) = true := by
  have h : ((childLL (childHH (childLH (childLH e24PhiAboveRoot))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childHH (childLH (childLH e24PhiAboveRoot)))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1131 :
    adaptiveCoverCheck 12 (childLH (childHH (childLH (childLH e24PhiAboveRoot)))) = true := by
  have h : ((childLH (childHH (childLH (childLH e24PhiAboveRoot))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childHH (childLH (childLH e24PhiAboveRoot)))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1132 :
    adaptiveCoverCheck 12 (childHL (childHH (childLH (childLH e24PhiAboveRoot)))) = true := by
  have h : ((childHL (childHH (childLH (childLH e24PhiAboveRoot))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childHH (childLH (childLH e24PhiAboveRoot)))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf1133 :
    adaptiveCoverCheck 12 (childHH (childHH (childLH (childLH e24PhiAboveRoot)))) = true := by
  have h : ((childHH (childHH (childLH (childLH e24PhiAboveRoot))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childHH (childLH (childLH e24PhiAboveRoot)))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf120 :
    adaptiveCoverCheck 13 (childLL (childHL (childLH e24PhiAboveRoot))) = true := by
  have h : ((childLL (childHL (childLH e24PhiAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL (childHL (childLH e24PhiAboveRoot))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf121 :
    adaptiveCoverCheck 13 (childLH (childHL (childLH e24PhiAboveRoot))) = true := by
  have h : ((childLH (childHL (childLH e24PhiAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH (childHL (childLH e24PhiAboveRoot))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf122 :
    adaptiveCoverCheck 13 (childHL (childHL (childLH e24PhiAboveRoot))) = true := by
  have h : ((childHL (childHL (childLH e24PhiAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childHL (childLH e24PhiAboveRoot))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf123 :
    adaptiveCoverCheck 13 (childHH (childHL (childLH e24PhiAboveRoot))) = true := by
  have h : ((childHH (childHL (childLH e24PhiAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childHL (childLH e24PhiAboveRoot))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf130 :
    adaptiveCoverCheck 13 (childLL (childHH (childLH e24PhiAboveRoot))) = true := by
  have h : ((childLL (childHH (childLH e24PhiAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL (childHH (childLH e24PhiAboveRoot))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf131 :
    adaptiveCoverCheck 13 (childLH (childHH (childLH e24PhiAboveRoot))) = true := by
  have h : ((childLH (childHH (childLH e24PhiAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH (childHH (childLH e24PhiAboveRoot))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf132 :
    adaptiveCoverCheck 13 (childHL (childHH (childLH e24PhiAboveRoot))) = true := by
  have h : ((childHL (childHH (childLH e24PhiAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childHH (childLH e24PhiAboveRoot))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf133 :
    adaptiveCoverCheck 13 (childHH (childHH (childLH e24PhiAboveRoot))) = true := by
  have h : ((childHH (childHH (childLH e24PhiAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childHH (childLH e24PhiAboveRoot))) h

theorem e24KC2PhiAboveLeaf2 :
    adaptiveCoverCheck 15 (childHL e24PhiAboveRoot) = true := by
  have h : physicallyIrrelevant (childHL e24PhiAboveRoot) = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_physicallyIrrelevant 15 (childHL e24PhiAboveRoot) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf300 :
    adaptiveCoverCheck 13 (childLL (childLL (childHH e24PhiAboveRoot))) = true := by
  have h : ((childLL (childLL (childHH e24PhiAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL (childLL (childHH e24PhiAboveRoot))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf301 :
    adaptiveCoverCheck 13 (childLH (childLL (childHH e24PhiAboveRoot))) = true := by
  have h : ((childLH (childLL (childHH e24PhiAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH (childLL (childHH e24PhiAboveRoot))) h

theorem e24KC2PhiAboveLeaf302 :
    adaptiveCoverCheck 13 (childHL (childLL (childHH e24PhiAboveRoot))) = true := by
  have h : physicallyIrrelevant (childHL (childLL (childHH e24PhiAboveRoot))) = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_physicallyIrrelevant 13 (childHL (childLL (childHH e24PhiAboveRoot))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf303 :
    adaptiveCoverCheck 13 (childHH (childLL (childHH e24PhiAboveRoot))) = true := by
  have h : ((childHH (childLL (childHH e24PhiAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLL (childHH e24PhiAboveRoot))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf310 :
    adaptiveCoverCheck 13 (childLL (childLH (childHH e24PhiAboveRoot))) = true := by
  have h : ((childLL (childLH (childHH e24PhiAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL (childLH (childHH e24PhiAboveRoot))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf311 :
    adaptiveCoverCheck 13 (childLH (childLH (childHH e24PhiAboveRoot))) = true := by
  have h : ((childLH (childLH (childHH e24PhiAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH (childLH (childHH e24PhiAboveRoot))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf312 :
    adaptiveCoverCheck 13 (childHL (childLH (childHH e24PhiAboveRoot))) = true := by
  have h : ((childHL (childLH (childHH e24PhiAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLH (childHH e24PhiAboveRoot))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf313 :
    adaptiveCoverCheck 13 (childHH (childLH (childHH e24PhiAboveRoot))) = true := by
  have h : ((childHH (childLH (childHH e24PhiAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLH (childHH e24PhiAboveRoot))) h

theorem e24KC2PhiAboveLeaf32 :
    adaptiveCoverCheck 14 (childHL (childHH e24PhiAboveRoot)) = true := by
  have h : physicallyIrrelevant (childHL (childHH e24PhiAboveRoot)) = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_physicallyIrrelevant 14 (childHL (childHH e24PhiAboveRoot)) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf330 :
    adaptiveCoverCheck 13 (childLL (childHH (childHH e24PhiAboveRoot))) = true := by
  have h : ((childLL (childHH (childHH e24PhiAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL (childHH (childHH e24PhiAboveRoot))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf331 :
    adaptiveCoverCheck 13 (childLH (childHH (childHH e24PhiAboveRoot))) = true := by
  have h : ((childLH (childHH (childHH e24PhiAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH (childHH (childHH e24PhiAboveRoot))) h

theorem e24KC2PhiAboveLeaf332 :
    adaptiveCoverCheck 13 (childHL (childHH (childHH e24PhiAboveRoot))) = true := by
  have h : physicallyIrrelevant (childHL (childHH (childHH e24PhiAboveRoot))) = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_physicallyIrrelevant 13 (childHL (childHH (childHH e24PhiAboveRoot))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiAboveLeaf333 :
    adaptiveCoverCheck 13 (childHH (childHH (childHH e24PhiAboveRoot))) = true := by
  have h : ((childHH (childHH (childHH e24PhiAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childHH (childHH e24PhiAboveRoot))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiBelowLeaf32212 :
    adaptiveCoverCheck 9 (childHL (childLH (childHL (childHL (childHH e24PhiBelowRoot))))) = true := by
  have h : ((childHL (childLH (childHL (childHL (childHH e24PhiBelowRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHL (childHL (childHH e24PhiBelowRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiBelowLeaf32220 :
    adaptiveCoverCheck 9 (childLL (childHL (childHL (childHL (childHH e24PhiBelowRoot))))) = true := by
  have h : ((childLL (childHL (childHL (childHL (childHH e24PhiBelowRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childHL (childHL (childHH e24PhiBelowRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiBelowLeaf32221 :
    adaptiveCoverCheck 9 (childLH (childHL (childHL (childHL (childHH e24PhiBelowRoot))))) = true := by
  have h : ((childLH (childHL (childHL (childHL (childHH e24PhiBelowRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childHL (childHL (childHH e24PhiBelowRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiBelowLeaf32222 :
    adaptiveCoverCheck 9 (childHL (childHL (childHL (childHL (childHH e24PhiBelowRoot))))) = true := by
  have h : ((childHL (childHL (childHL (childHL (childHH e24PhiBelowRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childHL (childHL (childHH e24PhiBelowRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiBelowLeaf32223 :
    adaptiveCoverCheck 9 (childHH (childHL (childHL (childHL (childHH e24PhiBelowRoot))))) = true := by
  have h : ((childHH (childHL (childHL (childHL (childHH e24PhiBelowRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childHL (childHL (childHH e24PhiBelowRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiBelowLeaf32230 :
    adaptiveCoverCheck 9 (childLL (childHH (childHL (childHL (childHH e24PhiBelowRoot))))) = true := by
  have h : ((childLL (childHH (childHL (childHL (childHH e24PhiBelowRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childHL (childHL (childHH e24PhiBelowRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiBelowLeaf32232 :
    adaptiveCoverCheck 9 (childHL (childHH (childHL (childHL (childHH e24PhiBelowRoot))))) = true := by
  have h : ((childHL (childHH (childHL (childHL (childHH e24PhiBelowRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childHL (childHL (childHH e24PhiBelowRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiBelowLeaf32233 :
    adaptiveCoverCheck 9 (childHH (childHH (childHL (childHL (childHH e24PhiBelowRoot))))) = true := by
  have h : ((childHH (childHH (childHL (childHL (childHH e24PhiBelowRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childHL (childHL (childHH e24PhiBelowRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiBelowLeaf33100 :
    adaptiveCoverCheck 9 (childLL (childLL (childLH (childHH (childHH e24PhiBelowRoot))))) = true := by
  have h : ((childLL (childLL (childLH (childHH (childHH e24PhiBelowRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childLH (childHH (childHH e24PhiBelowRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiBelowLeaf33101 :
    adaptiveCoverCheck 9 (childLH (childLL (childLH (childHH (childHH e24PhiBelowRoot))))) = true := by
  have h : ((childLH (childLL (childLH (childHH (childHH e24PhiBelowRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childLH (childHH (childHH e24PhiBelowRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiBelowLeaf33103 :
    adaptiveCoverCheck 9 (childHH (childLL (childLH (childHH (childHH e24PhiBelowRoot))))) = true := by
  have h : ((childHH (childLL (childLH (childHH (childHH e24PhiBelowRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childLH (childHH (childHH e24PhiBelowRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiBelowLeaf33110 :
    adaptiveCoverCheck 9 (childLL (childLH (childLH (childHH (childHH e24PhiBelowRoot))))) = true := by
  have h : ((childLL (childLH (childLH (childHH (childHH e24PhiBelowRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childLH (childHH (childHH e24PhiBelowRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiBelowLeaf33111 :
    adaptiveCoverCheck 9 (childLH (childLH (childLH (childHH (childHH e24PhiBelowRoot))))) = true := by
  have h : ((childLH (childLH (childLH (childHH (childHH e24PhiBelowRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childLH (childHH (childHH e24PhiBelowRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiBelowLeaf33112 :
    adaptiveCoverCheck 9 (childHL (childLH (childLH (childHH (childHH e24PhiBelowRoot))))) = true := by
  have h : ((childHL (childLH (childLH (childHH (childHH e24PhiBelowRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childLH (childHH (childHH e24PhiBelowRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiBelowLeaf33113 :
    adaptiveCoverCheck 9 (childHH (childLH (childLH (childHH (childHH e24PhiBelowRoot))))) = true := by
  have h : ((childHH (childLH (childLH (childHH (childHH e24PhiBelowRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childLH (childHH (childHH e24PhiBelowRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiBelowLeaf33130 :
    adaptiveCoverCheck 9 (childLL (childHH (childLH (childHH (childHH e24PhiBelowRoot))))) = true := by
  have h : ((childLL (childHH (childLH (childHH (childHH e24PhiBelowRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childLH (childHH (childHH e24PhiBelowRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiBelowLeaf33131 :
    adaptiveCoverCheck 9 (childLH (childHH (childLH (childHH (childHH e24PhiBelowRoot))))) = true := by
  have h : ((childLH (childHH (childLH (childHH (childHH e24PhiBelowRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childLH (childHH (childHH e24PhiBelowRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiBelowLeaf33133 :
    adaptiveCoverCheck 9 (childHH (childHH (childLH (childHH (childHH e24PhiBelowRoot))))) = true := by
  have h : ((childHH (childHH (childLH (childHH (childHH e24PhiBelowRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childLH (childHH (childHH e24PhiBelowRoot))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000000 :
    adaptiveCoverCheck 13 (childLL (childLL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))) = true := by
  have h : ((childLL (childLL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL (childLL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000001 :
    adaptiveCoverCheck 13 (childLH (childLL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))) = true := by
  have h : ((childLH (childLL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH (childLL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000002 :
    adaptiveCoverCheck 13 (childHL (childLL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))) = true := by
  have h : ((childHL (childLL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000003 :
    adaptiveCoverCheck 13 (childHH (childLL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))) = true := by
  have h : ((childHH (childLL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000010 :
    adaptiveCoverCheck 13 (childLL (childLH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))) = true := by
  have h : ((childLL (childLH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL (childLH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000011 :
    adaptiveCoverCheck 13 (childLH (childLH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))) = true := by
  have h : ((childLH (childLH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH (childLH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000012 :
    adaptiveCoverCheck 13 (childHL (childLH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))) = true := by
  have h : ((childHL (childLH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000013 :
    adaptiveCoverCheck 13 (childHH (childLH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))) = true := by
  have h : ((childHH (childLH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000200 :
    adaptiveCoverCheck 12 (childLL (childLL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childLL (childLL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000201 :
    adaptiveCoverCheck 12 (childLH (childLL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childLH (childLL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00002020 :
    adaptiveCoverCheck 11 (childLL (childHL (childLL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childHL (childLL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHL (childLL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00002021 :
    adaptiveCoverCheck 11 (childLH (childHL (childLL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childHL (childLL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHL (childLL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000020220 :
    adaptiveCoverCheck 10 (childLL (childHL (childHL (childLL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHL (childHL (childLL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHL (childHL (childLL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000020221 :
    adaptiveCoverCheck 10 (childLH (childHL (childHL (childLL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHL (childHL (childLL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHL (childHL (childLL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000020222 :
    adaptiveCoverCheck 10 (childHL (childHL (childHL (childLL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHL (childHL (childLL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childHL (childLL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000020223 :
    adaptiveCoverCheck 10 (childHH (childHL (childHL (childLL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHL (childHL (childLL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childHL (childLL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000020230 :
    adaptiveCoverCheck 10 (childLL (childHH (childHL (childLL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHH (childHL (childLL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHH (childHL (childLL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000020231 :
    adaptiveCoverCheck 10 (childLH (childHH (childHL (childLL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHH (childHL (childLL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHH (childHL (childLL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000020232 :
    adaptiveCoverCheck 10 (childHL (childHH (childHL (childLL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHH (childHL (childLL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childHL (childLL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000020233 :
    adaptiveCoverCheck 10 (childHH (childHH (childHL (childLL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHH (childHL (childLL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childHL (childLL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00002030 :
    adaptiveCoverCheck 11 (childLL (childHH (childLL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childHH (childLL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHH (childLL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00002031 :
    adaptiveCoverCheck 11 (childLH (childHH (childLL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childHH (childLL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHH (childLL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000020320 :
    adaptiveCoverCheck 10 (childLL (childHL (childHH (childLL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHL (childHH (childLL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHL (childHH (childLL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000020321 :
    adaptiveCoverCheck 10 (childLH (childHL (childHH (childLL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHL (childHH (childLL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHL (childHH (childLL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000020322 :
    adaptiveCoverCheck 10 (childHL (childHL (childHH (childLL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHL (childHH (childLL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childHH (childLL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000020323 :
    adaptiveCoverCheck 10 (childHH (childHL (childHH (childLL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHL (childHH (childLL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childHH (childLL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000020330 :
    adaptiveCoverCheck 10 (childLL (childHH (childHH (childLL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHH (childHH (childLL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHH (childHH (childLL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000020331 :
    adaptiveCoverCheck 10 (childLH (childHH (childHH (childLL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHH (childHH (childLL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHH (childHH (childLL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000020332 :
    adaptiveCoverCheck 10 (childHL (childHH (childHH (childLL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHH (childHH (childLL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childHH (childLL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000020333 :
    adaptiveCoverCheck 10 (childHH (childHH (childHH (childLL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHH (childHH (childLL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childHH (childLL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000210 :
    adaptiveCoverCheck 12 (childLL (childLH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childLL (childLH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000211 :
    adaptiveCoverCheck 12 (childLH (childLH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childLH (childLH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00002120 :
    adaptiveCoverCheck 11 (childLL (childHL (childLH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childHL (childLH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHL (childLH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00002121 :
    adaptiveCoverCheck 11 (childLH (childHL (childLH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childHL (childLH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHL (childLH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000021220 :
    adaptiveCoverCheck 10 (childLL (childHL (childHL (childLH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHL (childHL (childLH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHL (childHL (childLH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000021221 :
    adaptiveCoverCheck 10 (childLH (childHL (childHL (childLH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHL (childHL (childLH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHL (childHL (childLH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000021222 :
    adaptiveCoverCheck 10 (childHL (childHL (childHL (childLH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHL (childHL (childLH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childHL (childLH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000021223 :
    adaptiveCoverCheck 10 (childHH (childHL (childHL (childLH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHL (childHL (childLH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childHL (childLH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000021230 :
    adaptiveCoverCheck 10 (childLL (childHH (childHL (childLH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHH (childHL (childLH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHH (childHL (childLH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000021231 :
    adaptiveCoverCheck 10 (childLH (childHH (childHL (childLH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHH (childHL (childLH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHH (childHL (childLH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000021232 :
    adaptiveCoverCheck 10 (childHL (childHH (childHL (childLH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHH (childHL (childLH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childHL (childLH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000021233 :
    adaptiveCoverCheck 10 (childHH (childHH (childHL (childLH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHH (childHL (childLH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childHL (childLH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00002130 :
    adaptiveCoverCheck 11 (childLL (childHH (childLH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childHH (childLH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHH (childLH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00002131 :
    adaptiveCoverCheck 11 (childLH (childHH (childLH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childHH (childLH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHH (childLH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000021320 :
    adaptiveCoverCheck 10 (childLL (childHL (childHH (childLH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHL (childHH (childLH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHL (childHH (childLH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000021321 :
    adaptiveCoverCheck 10 (childLH (childHL (childHH (childLH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHL (childHH (childLH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHL (childHH (childLH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000021322 :
    adaptiveCoverCheck 10 (childHL (childHL (childHH (childLH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHL (childHH (childLH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childHH (childLH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000021323 :
    adaptiveCoverCheck 10 (childHH (childHL (childHH (childLH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHL (childHH (childLH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childHH (childLH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000021330 :
    adaptiveCoverCheck 10 (childLL (childHH (childHH (childLH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHH (childHH (childLH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHH (childHH (childLH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000021331 :
    adaptiveCoverCheck 10 (childLH (childHH (childHH (childLH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHH (childHH (childLH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHH (childHH (childLH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000021332 :
    adaptiveCoverCheck 10 (childHL (childHH (childHH (childLH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHH (childHH (childLH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childHH (childLH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000021333 :
    adaptiveCoverCheck 10 (childHH (childHH (childHH (childLH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHH (childHH (childLH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childHH (childLH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000220000 :
    adaptiveCoverCheck 9 (childLL (childLL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000220001 :
    adaptiveCoverCheck 9 (childLH (childLL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000220010 :
    adaptiveCoverCheck 9 (childLL (childLH (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000220011 :
    adaptiveCoverCheck 9 (childLH (childLH (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childLL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000220100 :
    adaptiveCoverCheck 9 (childLL (childLL (childLH (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childLH (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childLH (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000220101 :
    adaptiveCoverCheck 9 (childLH (childLL (childLH (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childLH (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childLH (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000220110 :
    adaptiveCoverCheck 9 (childLL (childLH (childLH (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childLH (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childLH (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000220111 :
    adaptiveCoverCheck 9 (childLH (childLH (childLH (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childLH (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childLH (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000022020 :
    adaptiveCoverCheck 10 (childLL (childHL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000022021 :
    adaptiveCoverCheck 10 (childLH (childHL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000022022 :
    adaptiveCoverCheck 10 (childHL (childHL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000022023 :
    adaptiveCoverCheck 10 (childHH (childHL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000022030 :
    adaptiveCoverCheck 10 (childLL (childHH (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHH (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHH (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000022031 :
    adaptiveCoverCheck 10 (childLH (childHH (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHH (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHH (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000022032 :
    adaptiveCoverCheck 10 (childHL (childHH (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHH (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000022033 :
    adaptiveCoverCheck 10 (childHH (childHH (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHH (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childLL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000221000 :
    adaptiveCoverCheck 9 (childLL (childLL (childLL (childLH (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childLL (childLH (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childLL (childLH (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000221001 :
    adaptiveCoverCheck 9 (childLH (childLL (childLL (childLH (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childLL (childLH (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childLL (childLH (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000221010 :
    adaptiveCoverCheck 9 (childLL (childLH (childLL (childLH (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childLL (childLH (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childLL (childLH (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000221011 :
    adaptiveCoverCheck 9 (childLH (childLH (childLL (childLH (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childLL (childLH (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childLL (childLH (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000221100 :
    adaptiveCoverCheck 9 (childLL (childLL (childLH (childLH (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childLH (childLH (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childLH (childLH (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000221101 :
    adaptiveCoverCheck 9 (childLH (childLL (childLH (childLH (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childLH (childLH (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childLH (childLH (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000221110 :
    adaptiveCoverCheck 9 (childLL (childLH (childLH (childLH (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childLH (childLH (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childLH (childLH (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000221111 :
    adaptiveCoverCheck 9 (childLH (childLH (childLH (childLH (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childLH (childLH (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childLH (childLH (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000022120 :
    adaptiveCoverCheck 10 (childLL (childHL (childLH (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHL (childLH (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHL (childLH (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000022121 :
    adaptiveCoverCheck 10 (childLH (childHL (childLH (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHL (childLH (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHL (childLH (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000022122 :
    adaptiveCoverCheck 10 (childHL (childHL (childLH (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHL (childLH (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childLH (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000022123 :
    adaptiveCoverCheck 10 (childHH (childHL (childLH (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHL (childLH (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childLH (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000022130 :
    adaptiveCoverCheck 10 (childLL (childHH (childLH (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHH (childLH (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHH (childLH (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000221310 :
    adaptiveCoverCheck 9 (childLL (childLH (childHH (childLH (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childHH (childLH (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHH (childLH (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000221311 :
    adaptiveCoverCheck 9 (childLH (childLH (childHH (childLH (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childHH (childLH (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHH (childLH (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000221312 :
    adaptiveCoverCheck 9 (childHL (childLH (childHH (childLH (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHH (childLH (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHH (childLH (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000221313 :
    adaptiveCoverCheck 9 (childHH (childLH (childHH (childLH (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHH (childLH (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHH (childLH (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000022132 :
    adaptiveCoverCheck 10 (childHL (childHH (childLH (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHH (childLH (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childLH (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000022133 :
    adaptiveCoverCheck 10 (childHH (childHH (childLH (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHH (childLH (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childLH (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00002220 :
    adaptiveCoverCheck 11 (childLL (childHL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childHL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00002221 :
    adaptiveCoverCheck 11 (childLH (childHL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childHL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00002222 :
    adaptiveCoverCheck 11 (childHL (childHL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00002223 :
    adaptiveCoverCheck 11 (childHH (childHL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00002230 :
    adaptiveCoverCheck 11 (childLL (childHH (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childHH (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHH (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00002231 :
    adaptiveCoverCheck 11 (childLH (childHH (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childHH (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHH (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00002232 :
    adaptiveCoverCheck 11 (childHL (childHH (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHH (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00002233 :
    adaptiveCoverCheck 11 (childHH (childHH (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHH (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childHL (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000230000 :
    adaptiveCoverCheck 9 (childLL (childLL (childLL (childLL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childLL (childLL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childLL (childLL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000230001 :
    adaptiveCoverCheck 9 (childLH (childLL (childLL (childLL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childLL (childLL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childLL (childLL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000230010 :
    adaptiveCoverCheck 9 (childLL (childLH (childLL (childLL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childLL (childLL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childLL (childLL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000230011 :
    adaptiveCoverCheck 9 (childLH (childLH (childLL (childLL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childLL (childLL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childLL (childLL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000230100 :
    adaptiveCoverCheck 9 (childLL (childLL (childLH (childLL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childLH (childLL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childLH (childLL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000230101 :
    adaptiveCoverCheck 9 (childLH (childLL (childLH (childLL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childLH (childLL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childLH (childLL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000230110 :
    adaptiveCoverCheck 9 (childLL (childLH (childLH (childLL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childLH (childLL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childLH (childLL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000230111 :
    adaptiveCoverCheck 9 (childLH (childLH (childLH (childLL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childLH (childLL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childLH (childLL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000230200 :
    adaptiveCoverCheck 9 (childLL (childLL (childHL (childLL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHL (childLL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHL (childLL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000230201 :
    adaptiveCoverCheck 9 (childLH (childLL (childHL (childLL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHL (childLL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHL (childLL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000230202 :
    adaptiveCoverCheck 9 (childHL (childLL (childHL (childLL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHL (childLL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHL (childLL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000230203 :
    adaptiveCoverCheck 9 (childHH (childLL (childHL (childLL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHL (childLL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHL (childLL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000230210 :
    adaptiveCoverCheck 9 (childLL (childLH (childHL (childLL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childHL (childLL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHL (childLL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000230211 :
    adaptiveCoverCheck 9 (childLH (childLH (childHL (childLL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childHL (childLL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHL (childLL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000230212 :
    adaptiveCoverCheck 9 (childHL (childLH (childHL (childLL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHL (childLL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHL (childLL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000230213 :
    adaptiveCoverCheck 9 (childHH (childLH (childHL (childLL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHL (childLL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHL (childLL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000023022 :
    adaptiveCoverCheck 10 (childHL (childHL (childLL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHL (childLL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childLL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000023023 :
    adaptiveCoverCheck 10 (childHH (childHL (childLL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHL (childLL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childLL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000230300 :
    adaptiveCoverCheck 9 (childLL (childLL (childHH (childLL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHH (childLL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHH (childLL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000230301 :
    adaptiveCoverCheck 9 (childLH (childLL (childHH (childLL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHH (childLL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHH (childLL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000230302 :
    adaptiveCoverCheck 9 (childHL (childLL (childHH (childLL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHH (childLL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHH (childLL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000230303 :
    adaptiveCoverCheck 9 (childHH (childLL (childHH (childLL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHH (childLL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHH (childLL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000230310 :
    adaptiveCoverCheck 9 (childLL (childLH (childHH (childLL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childHH (childLL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHH (childLL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000230311 :
    adaptiveCoverCheck 9 (childLH (childLH (childHH (childLL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childHH (childLL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHH (childLL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000230312 :
    adaptiveCoverCheck 9 (childHL (childLH (childHH (childLL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHH (childLL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHH (childLL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000230313 :
    adaptiveCoverCheck 9 (childHH (childLH (childHH (childLL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHH (childLL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHH (childLL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000023032 :
    adaptiveCoverCheck 10 (childHL (childHH (childLL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHH (childLL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childLL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000023033 :
    adaptiveCoverCheck 10 (childHH (childHH (childLL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHH (childLL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childLL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000231000 :
    adaptiveCoverCheck 9 (childLL (childLL (childLL (childLH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childLL (childLH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childLL (childLH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000231001 :
    adaptiveCoverCheck 9 (childLH (childLL (childLL (childLH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childLL (childLH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childLL (childLH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000231010 :
    adaptiveCoverCheck 9 (childLL (childLH (childLL (childLH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childLL (childLH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childLL (childLH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000231011 :
    adaptiveCoverCheck 9 (childLH (childLH (childLL (childLH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childLL (childLH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childLL (childLH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000231100 :
    adaptiveCoverCheck 9 (childLL (childLL (childLH (childLH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childLH (childLH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childLH (childLH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000231101 :
    adaptiveCoverCheck 9 (childLH (childLL (childLH (childLH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childLH (childLH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childLH (childLH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000231110 :
    adaptiveCoverCheck 9 (childLL (childLH (childLH (childLH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childLH (childLH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childLH (childLH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000231111 :
    adaptiveCoverCheck 9 (childLH (childLH (childLH (childLH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childLH (childLH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childLH (childLH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000231200 :
    adaptiveCoverCheck 9 (childLL (childLL (childHL (childLH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHL (childLH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHL (childLH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000231201 :
    adaptiveCoverCheck 9 (childLH (childLL (childHL (childLH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHL (childLH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHL (childLH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000231202 :
    adaptiveCoverCheck 9 (childHL (childLL (childHL (childLH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHL (childLH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHL (childLH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000231203 :
    adaptiveCoverCheck 9 (childHH (childLL (childHL (childLH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHL (childLH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHL (childLH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000231210 :
    adaptiveCoverCheck 9 (childLL (childLH (childHL (childLH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childHL (childLH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHL (childLH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000231211 :
    adaptiveCoverCheck 9 (childLH (childLH (childHL (childLH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childHL (childLH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHL (childLH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000231212 :
    adaptiveCoverCheck 9 (childHL (childLH (childHL (childLH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHL (childLH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHL (childLH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000231213 :
    adaptiveCoverCheck 9 (childHH (childLH (childHL (childLH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHL (childLH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHL (childLH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000023122 :
    adaptiveCoverCheck 10 (childHL (childHL (childLH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHL (childLH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childLH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000023123 :
    adaptiveCoverCheck 10 (childHH (childHL (childLH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHL (childLH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childLH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000231300 :
    adaptiveCoverCheck 9 (childLL (childLL (childHH (childLH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLL (childHH (childLH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childHH (childLH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000231301 :
    adaptiveCoverCheck 9 (childLH (childLL (childHH (childLH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLL (childHH (childLH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childHH (childLH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000231302 :
    adaptiveCoverCheck 9 (childHL (childLL (childHH (childLH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLL (childHH (childLH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childHH (childLH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000231303 :
    adaptiveCoverCheck 9 (childHH (childLL (childHH (childLH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLL (childHH (childLH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childHH (childLH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000231310 :
    adaptiveCoverCheck 9 (childLL (childLH (childHH (childLH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLL (childLH (childHH (childLH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childHH (childLH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000231311 :
    adaptiveCoverCheck 9 (childLH (childLH (childHH (childLH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childLH (childLH (childHH (childLH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childHH (childLH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000231312 :
    adaptiveCoverCheck 9 (childHL (childLH (childHH (childLH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHL (childLH (childHH (childLH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childHH (childLH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000231313 :
    adaptiveCoverCheck 9 (childHH (childLH (childHH (childLH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) = true := by
  have h : ((childHH (childLH (childHH (childLH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childHH (childLH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000023132 :
    adaptiveCoverCheck 10 (childHL (childHH (childLH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHH (childLH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childLH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000023133 :
    adaptiveCoverCheck 10 (childHH (childHH (childLH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHH (childLH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childLH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00002320 :
    adaptiveCoverCheck 11 (childLL (childHL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childHL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00002321 :
    adaptiveCoverCheck 11 (childLH (childHL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childHL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00002322 :
    adaptiveCoverCheck 11 (childHL (childHL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00002323 :
    adaptiveCoverCheck 11 (childHH (childHL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00002330 :
    adaptiveCoverCheck 11 (childLL (childHH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childHH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00002331 :
    adaptiveCoverCheck 11 (childLH (childHH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childHH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00002332 :
    adaptiveCoverCheck 11 (childHL (childHH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHL (childHH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00002333 :
    adaptiveCoverCheck 11 (childHH (childHH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childHH (childHH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childHH (childHL (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000300 :
    adaptiveCoverCheck 12 (childLL (childLL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childLL (childLL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000301 :
    adaptiveCoverCheck 12 (childLH (childLL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childLH (childLL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00003020 :
    adaptiveCoverCheck 11 (childLL (childHL (childLL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childHL (childLL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHL (childLL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00003021 :
    adaptiveCoverCheck 11 (childLH (childHL (childLL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childHL (childLL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHL (childLL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000030220 :
    adaptiveCoverCheck 10 (childLL (childHL (childHL (childLL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHL (childHL (childLL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHL (childHL (childLL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000030221 :
    adaptiveCoverCheck 10 (childLH (childHL (childHL (childLL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHL (childHL (childLL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHL (childHL (childLL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000030222 :
    adaptiveCoverCheck 10 (childHL (childHL (childHL (childLL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHL (childHL (childLL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childHL (childLL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000030223 :
    adaptiveCoverCheck 10 (childHH (childHL (childHL (childLL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHL (childHL (childLL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childHL (childLL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000030230 :
    adaptiveCoverCheck 10 (childLL (childHH (childHL (childLL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHH (childHL (childLL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHH (childHL (childLL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000030231 :
    adaptiveCoverCheck 10 (childLH (childHH (childHL (childLL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHH (childHL (childLL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHH (childHL (childLL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000030232 :
    adaptiveCoverCheck 10 (childHL (childHH (childHL (childLL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHH (childHL (childLL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childHL (childLL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000030233 :
    adaptiveCoverCheck 10 (childHH (childHH (childHL (childLL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHH (childHL (childLL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childHL (childLL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00003030 :
    adaptiveCoverCheck 11 (childLL (childHH (childLL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childHH (childLL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHH (childLL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00003031 :
    adaptiveCoverCheck 11 (childLH (childHH (childLL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLH (childHH (childLL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHH (childLL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000030320 :
    adaptiveCoverCheck 10 (childLL (childHL (childHH (childLL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHL (childHH (childLL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHL (childHH (childLL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000030321 :
    adaptiveCoverCheck 10 (childLH (childHL (childHH (childLL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHL (childHH (childLL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHL (childHH (childLL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000030322 :
    adaptiveCoverCheck 10 (childHL (childHL (childHH (childLL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHL (childHH (childLL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL (childHH (childLL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000030323 :
    adaptiveCoverCheck 10 (childHH (childHL (childHH (childLL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHL (childHH (childLL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL (childHH (childLL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000030330 :
    adaptiveCoverCheck 10 (childLL (childHH (childHH (childLL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLL (childHH (childHH (childLL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHH (childHH (childLL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000030331 :
    adaptiveCoverCheck 10 (childLH (childHH (childHH (childLL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childLH (childHH (childHH (childLL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHH (childHH (childLL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000030332 :
    adaptiveCoverCheck 10 (childHL (childHH (childHH (childLL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHL (childHH (childHH (childLL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH (childHH (childLL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf000030333 :
    adaptiveCoverCheck 10 (childHH (childHH (childHH (childLL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) = true := by
  have h : ((childHH (childHH (childHH (childLL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH (childHH (childLL (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000310 :
    adaptiveCoverCheck 12 (childLL (childLH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childLL (childLH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf0000311 :
    adaptiveCoverCheck 12 (childLH (childLH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))) = true := by
  have h : ((childLH (childLH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))) h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2ThetaAboveLeaf00003120 :
    adaptiveCoverCheck 11 (childLL (childHL (childLH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) = true := by
  have h : ((childLL (childHL (childLH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot))))))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHL (childLH (childHH (childLL (childLL (childLL (childLL e24ThetaAboveRoot)))))))) h

end PartE
end GerverSofa
