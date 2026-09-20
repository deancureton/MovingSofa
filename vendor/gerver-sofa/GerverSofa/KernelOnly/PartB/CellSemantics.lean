import GerverSofa.KernelOnly.PartB.Phase1Semantics
import GerverSofa.KernelOnly.PartB.Phase2Semantics
import GerverSofa.KernelOnly.PartB.Phase3Semantics
import GerverSofa.KernelOnly.PartB.Phase4Semantics
import GerverSofa.KernelOnly.PartB.Phase5Semantics

/-!
# Assembly of semantic soundness for the Part B cell certificate

The five phase enclosures are independent modules.  This file classifies the
four switching cells, selects the appropriate phase/hull, and proves semantic
soundness of the two product-cell support expressions.
-/

noncomputable section

namespace GerverSofa
namespace PartB

open RatInterval

/-! ## Switches lie in exactly four mesh cells -/

private theorem node1_lt_phi : nodeTime 1 < params.phi := by
  have hpi : Real.pi ≤ (ExactReplay.piI.hi : ℝ) :=
    ExactReplay.piI_contains_pi.2
  have hp := phi_bounds.1
  unfold nodeTime nodeCoeff
  norm_num [ExactReplay.piI, ExactReplay.q] at hpi hp ⊢
  nlinarith

private theorem phi_lt_node2 : params.phi < nodeTime 2 := by
  have hpi : (ExactReplay.piI.lo : ℝ) ≤ Real.pi :=
    ExactReplay.piI_contains_pi.1
  have hp := phi_bounds.2
  unfold nodeTime nodeCoeff
  norm_num [ExactReplay.piI, ExactReplay.q] at hpi hp ⊢
  nlinarith

private theorem node27_lt_theta : nodeTime 27 < params.theta := by
  have hpi : Real.pi ≤ (ExactReplay.piI.hi : ℝ) :=
    ExactReplay.piI_contains_pi.2
  have hp := theta_bounds.1
  unfold nodeTime nodeCoeff
  norm_num [ExactReplay.piI, ExactReplay.q] at hpi hp ⊢
  nlinarith

private theorem theta_lt_node28 : params.theta < nodeTime 28 := by
  have hpi : (ExactReplay.piI.lo : ℝ) ≤ Real.pi :=
    ExactReplay.piI_contains_pi.1
  have hp := theta_bounds.2
  unfold nodeTime nodeCoeff
  norm_num [ExactReplay.piI, ExactReplay.q] at hpi hp ⊢
  nlinarith

private theorem node36_lt_eta :
    nodeTime 36 < Real.pi / 2 - params.theta := by
  have h := theta_lt_node28
  unfold nodeTime nodeCoeff at h ⊢
  norm_num at h ⊢
  linarith

private theorem eta_lt_node37 :
    Real.pi / 2 - params.theta < nodeTime 37 := by
  have h := node27_lt_theta
  unfold nodeTime nodeCoeff at h ⊢
  norm_num at h ⊢
  linarith

private theorem node62_lt_tau :
    nodeTime 62 < Real.pi / 2 - params.phi := by
  have h := phi_lt_node2
  unfold nodeTime nodeCoeff at h ⊢
  norm_num at h ⊢
  linarith

private theorem tau_lt_node63 :
    Real.pi / 2 - params.phi < nodeTime 63 := by
  have h := node1_lt_phi
  unfold nodeTime nodeCoeff at h ⊢
  norm_num at h ⊢
  linarith

private theorem phase1_cell {i : Cell} {t : ℝ}
    (ht : t ∈ cellSet i) (hphase : t ≤ params.phi) : i.1 ≤ 1 := by
  by_contra hnot
  have hi : 2 ≤ i.1 := by omega
  have h2i : nodeTime 2 ≤ nodeTime i.1 := nodeTime_mono hi
  linarith [phi_lt_node2, ht.1]

private theorem phase2_cell {i : Cell} {t : ℝ}
    (ht : t ∈ cellSet i) (hlo : params.phi < t)
    (hhi : t ≤ params.theta) : 1 ≤ i.1 ∧ i.1 ≤ 27 := by
  constructor
  · by_contra hnot
    have hi0 : i.1 = 0 := by omega
    have hend : t ≤ nodeTime 1 := by simpa [cellSet, hi0] using ht.2
    linarith [node1_lt_phi]
  · by_contra hnot
    have hi : 28 ≤ i.1 := by omega
    have h28i : nodeTime 28 ≤ nodeTime i.1 := nodeTime_mono hi
    linarith [theta_lt_node28, ht.1]

private theorem phase3_cell {i : Cell} {t : ℝ}
    (ht : t ∈ cellSet i) (hlo : params.theta < t)
    (hhi : t ≤ Real.pi / 2 - params.theta) :
    27 ≤ i.1 ∧ i.1 ≤ 36 := by
  constructor
  · by_contra hnot
    have hi : i.1 + 1 ≤ 27 := by omega
    have hend : nodeTime (i.1 + 1) ≤ nodeTime 27 := nodeTime_mono hi
    linarith [node27_lt_theta, ht.2]
  · by_contra hnot
    have hi : 37 ≤ i.1 := by omega
    have h37i : nodeTime 37 ≤ nodeTime i.1 := nodeTime_mono hi
    linarith [eta_lt_node37, ht.1]

private theorem phase4_cell {i : Cell} {t : ℝ}
    (ht : t ∈ cellSet i)
    (hlo : Real.pi / 2 - params.theta < t)
    (hhi : t ≤ Real.pi / 2 - params.phi) :
    36 ≤ i.1 ∧ i.1 ≤ 62 := by
  constructor
  · by_contra hnot
    have hi : i.1 + 1 ≤ 36 := by omega
    have hend : nodeTime (i.1 + 1) ≤ nodeTime 36 := nodeTime_mono hi
    linarith [node36_lt_eta, ht.2]
  · by_contra hnot
    have hi : 63 ≤ i.1 := by omega
    have h63i : nodeTime 63 ≤ nodeTime i.1 := nodeTime_mono hi
    linarith [tau_lt_node63, ht.1]

private theorem phase5_cell {i : Cell} {t : ℝ}
    (ht : t ∈ cellSet i)
    (hlo : Real.pi / 2 - params.phi < t) : 62 ≤ i.1 := by
  by_contra hnot
  have hi : i.1 + 1 ≤ 62 := by omega
  have hend : nodeTime (i.1 + 1) ≤ nodeTime 62 := nodeTime_mono hi
  linarith [node62_lt_tau, ht.2]

/-! ## Every literal path branch is contained in the selected cell hull -/

private theorem cellPath_contains_piece1 {i : Cell} {t : ℝ}
    (htCell : t ∈ cellSet i) (htPhys : t ∈ physicalInterval)
    (hi : i.1 ≤ 1) :
    PointContains (cellPathInterval i) (Romik.path1 params t) := by
  have h := cellPiece1_contains htCell htPhys
  by_cases h0 : i.1 = 0
  · simpa [cellPathInterval, h0] using h
  · have h1 : i.1 = 1 := by omega
    simpa [cellPathInterval, h0, h1] using pointContains_hull_left h

private theorem cellPath_contains_piece2 {i : Cell} {t : ℝ}
    (htCell : t ∈ cellSet i) (htPhys : t ∈ physicalInterval)
    (hi : 1 ≤ i.1 ∧ i.1 ≤ 27) :
    PointContains (cellPathInterval i) (Romik.path2 params t) := by
  have h := cellPiece2_contains htCell htPhys
  by_cases h1 : i.1 = 1
  · have h0 : i.1 ≠ 0 := by omega
    simpa [cellPathInterval, h0, h1] using pointContains_hull_right h
  by_cases h27 : i.1 = 27
  · have h0 : i.1 ≠ 0 := by omega
    have h26 : ¬ i.1 ≤ 26 := by omega
    simpa [cellPathInterval, h0, h1, h26, h27] using pointContains_hull_left h
  · have h0 : i.1 ≠ 0 := by omega
    have h26 : i.1 ≤ 26 := by omega
    simpa [cellPathInterval, h0, h1, h26] using h

private theorem cellPath_contains_piece3 {i : Cell} {t : ℝ}
    (htCell : t ∈ cellSet i) (htPhys : t ∈ physicalInterval)
    (hi : 27 ≤ i.1 ∧ i.1 ≤ 36) :
    PointContains (cellPathInterval i) (Romik.path3 params t) := by
  have h := cellPiece3_contains htCell htPhys
  by_cases h27 : i.1 = 27
  · have h0 : i.1 ≠ 0 := by omega
    have h1 : i.1 ≠ 1 := by omega
    have h26 : ¬ i.1 ≤ 26 := by omega
    simpa [cellPathInterval, h0, h1, h26, h27] using pointContains_hull_right h
  by_cases h36 : i.1 = 36
  · have h0 : i.1 ≠ 0 := by omega
    have h1 : i.1 ≠ 1 := by omega
    have h26 : ¬ i.1 ≤ 26 := by omega
    have h27n : i.1 ≠ 27 := by omega
    have h35 : ¬ i.1 ≤ 35 := by omega
    simpa [cellPathInterval, h0, h1, h26, h27n, h35, h36] using
      pointContains_hull_left h
  · have h0 : i.1 ≠ 0 := by omega
    have h1 : i.1 ≠ 1 := by omega
    have h26 : ¬ i.1 ≤ 26 := by omega
    have h27n : i.1 ≠ 27 := by omega
    have h35 : i.1 ≤ 35 := by omega
    simpa [cellPathInterval, h0, h1, h26, h27n, h35] using h

private theorem cellPath_contains_piece4 {i : Cell} {t : ℝ}
    (htCell : t ∈ cellSet i) (htPhys : t ∈ physicalInterval)
    (hi : 36 ≤ i.1 ∧ i.1 ≤ 62) :
    PointContains (cellPathInterval i) (Romik.path4 params t) := by
  have h := cellPiece4_contains htCell htPhys
  by_cases h36 : i.1 = 36
  · have h0 : i.1 ≠ 0 := by omega
    have h1 : i.1 ≠ 1 := by omega
    have h26 : ¬ i.1 ≤ 26 := by omega
    have h27 : i.1 ≠ 27 := by omega
    have h35 : ¬ i.1 ≤ 35 := by omega
    simpa [cellPathInterval, h0, h1, h26, h27, h35, h36] using
      pointContains_hull_right h
  by_cases h62 : i.1 = 62
  · have h0 : i.1 ≠ 0 := by omega
    have h1 : i.1 ≠ 1 := by omega
    have h26 : ¬ i.1 ≤ 26 := by omega
    have h27 : i.1 ≠ 27 := by omega
    have h35 : ¬ i.1 ≤ 35 := by omega
    have h36n : i.1 ≠ 36 := by omega
    have h61 : ¬ i.1 ≤ 61 := by omega
    simpa [cellPathInterval, h0, h1, h26, h27, h35, h36n, h61, h62] using
      pointContains_hull_left h
  · have h0 : i.1 ≠ 0 := by omega
    have h1 : i.1 ≠ 1 := by omega
    have h26 : ¬ i.1 ≤ 26 := by omega
    have h27 : i.1 ≠ 27 := by omega
    have h35 : ¬ i.1 ≤ 35 := by omega
    have h36n : i.1 ≠ 36 := by omega
    have h61 : i.1 ≤ 61 := by omega
    simpa [cellPathInterval, h0, h1, h26, h27, h35, h36n, h61] using h

private theorem cellPath_contains_piece5 {i : Cell} {t : ℝ}
    (htCell : t ∈ cellSet i) (htPhys : t ∈ physicalInterval)
    (hi : 62 ≤ i.1) :
    PointContains (cellPathInterval i) (Romik.path5 params t) := by
  have h := cellPiece5_contains htCell htPhys
  by_cases h62 : i.1 = 62
  · have h0 : i.1 ≠ 0 := by omega
    have h1 : i.1 ≠ 1 := by omega
    have h26 : ¬ i.1 ≤ 26 := by omega
    have h27 : i.1 ≠ 27 := by omega
    have h35 : ¬ i.1 ≤ 35 := by omega
    have h36 : i.1 ≠ 36 := by omega
    have h61 : ¬ i.1 ≤ 61 := by omega
    simpa [cellPathInterval, h0, h1, h26, h27, h35, h36, h61, h62] using
      pointContains_hull_right h
  · have h63 : i.1 = 63 := by omega
    have h0 : i.1 ≠ 0 := by omega
    have h1 : i.1 ≠ 1 := by omega
    have h26 : ¬ i.1 ≤ 26 := by omega
    have h27 : i.1 ≠ 27 := by omega
    have h35 : ¬ i.1 ≤ 35 := by omega
    have h36 : i.1 ≠ 36 := by omega
    have h61 : ¬ i.1 ≤ 61 := by omega
    have h62n : i.1 ≠ 62 := by omega
    simpa [cellPathInterval, h0, h1, h26, h27, h35, h36, h61, h62n,
      h63] using h

/-- The interval selected for a cell contains the literal five-phase path at
every physical time in that cell. -/
theorem cellPath_contains {i : Cell} {t : ℝ}
    (htCell : t ∈ cellSet i) (htPhys : t ∈ physicalInterval) :
    PointContains (cellPathInterval i) (Romik.path params t) := by
  unfold Romik.path
  by_cases h1 : t ≤ params.phi
  · rw [if_pos h1]
    exact cellPath_contains_piece1 htCell htPhys (phase1_cell htCell h1)
  · rw [if_neg h1]
    have h1' : params.phi < t := lt_of_not_ge h1
    by_cases h2 : t ≤ params.theta
    · rw [if_pos h2]
      exact cellPath_contains_piece2 htCell htPhys
        (phase2_cell htCell h1' h2)
    · rw [if_neg h2]
      have h2' : params.theta < t := lt_of_not_ge h2
      by_cases h3 : t ≤ Real.pi / 2 - params.theta
      · rw [if_pos h3]
        exact cellPath_contains_piece3 htCell htPhys
          (phase3_cell htCell h2' h3)
      · rw [if_neg h3]
        have h3' : Real.pi / 2 - params.theta < t := lt_of_not_ge h3
        by_cases h4 : t ≤ Real.pi / 2 - params.phi
        · rw [if_pos h4]
          exact cellPath_contains_piece4 htCell htPhys
            (phase4_cell htCell h3' h4)
        · rw [if_neg h4]
          have h4' : Real.pi / 2 - params.phi < t := lt_of_not_ge h4
          exact cellPath_contains_piece5 htCell htPhys
            (phase5_cell htCell h4')

/-! ## Semantic soundness of the two product-cell expressions -/

theorem guCell_contains {i j : Cell} {s t : ℝ}
    (hsCell : s ∈ cellSet i) (htCell : t ∈ cellSet j)
    (hsPhys : s ∈ physicalInterval) (htPhys : t ∈ physicalInterval) :
    Contains (guCellInterval i j) (Gu s t) := by
  have hxs := cellPath_contains hsCell hsPhys
  have hxt := cellPath_contains htCell htPhys
  have htr := trig_contains hsCell hsPhys
  have hdx := RatInterval.contains_sub hxs.1 hxt.1
  have hdy := RatInterval.contains_sub hxs.2 hxt.2
  have hone := point_contains 1
  have h := RatInterval.contains_add
    (RatInterval.contains_add hone (RatInterval.contains_mul hdx htr.1))
    (RatInterval.contains_mul hdy htr.2)
  simpa [guCellInterval, Gu, dot, u, sub_eq_add_neg, ExactReplay.oneI, add_assoc] using h

theorem gvCell_contains {i j : Cell} {s t : ℝ}
    (hsCell : s ∈ cellSet i) (htCell : t ∈ cellSet j)
    (hsPhys : s ∈ physicalInterval) (htPhys : t ∈ physicalInterval) :
    Contains (gvCellInterval i j) (Gv s t) := by
  have hxs := cellPath_contains hsCell hsPhys
  have hxt := cellPath_contains htCell htPhys
  have htr := trig_contains hsCell hsPhys
  have hdx := RatInterval.contains_sub hxs.1 hxt.1
  have hdy := RatInterval.contains_sub hxs.2 hxt.2
  have hone := point_contains 1
  have h := RatInterval.contains_add
    (RatInterval.contains_add hone
      (RatInterval.contains_mul hdx (RatInterval.contains_neg htr.2)))
    (RatInterval.contains_mul hdy htr.1)
  simpa [gvCellInterval, Gv, dot, v, sub_eq_add_neg, ExactReplay.oneI, add_assoc] using h

end PartB
end GerverSofa
