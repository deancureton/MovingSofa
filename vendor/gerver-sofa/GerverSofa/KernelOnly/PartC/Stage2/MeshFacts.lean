import GerverSofa.KernelOnly.PartC.GeometrySpec

/-!
# Part C Stage 2 public mesh and branch facts

This module exposes the switch-cell classification already used internally in
Part B.  It is deliberately proved again from the frozen angle boxes so that
Part C contact and no-hidden-crossing certificates can reuse the exact 64-cell
mesh without depending on private declarations.
-/

noncomputable section

namespace GerverSofa
namespace PartC
namespace Stage2

open RatInterval

 theorem node1_lt_phi : PartB.nodeTime 1 < params.phi := by
  have hpi : Real.pi ≤ (ExactReplay.piI.hi : ℝ) :=
    ExactReplay.piI_contains_pi.2
  have hp := phi_bounds.1
  unfold PartB.nodeTime PartB.nodeCoeff
  norm_num [ExactReplay.piI, ExactReplay.q] at hpi hp ⊢
  nlinarith

 theorem phi_lt_node2 : params.phi < PartB.nodeTime 2 := by
  have hpi : (ExactReplay.piI.lo : ℝ) ≤ Real.pi :=
    ExactReplay.piI_contains_pi.1
  have hp := phi_bounds.2
  unfold PartB.nodeTime PartB.nodeCoeff
  norm_num [ExactReplay.piI, ExactReplay.q] at hpi hp ⊢
  nlinarith

 theorem node27_lt_theta : PartB.nodeTime 27 < params.theta := by
  have hpi : Real.pi ≤ (ExactReplay.piI.hi : ℝ) :=
    ExactReplay.piI_contains_pi.2
  have hp := theta_bounds.1
  unfold PartB.nodeTime PartB.nodeCoeff
  norm_num [ExactReplay.piI, ExactReplay.q] at hpi hp ⊢
  nlinarith

 theorem theta_lt_node28 : params.theta < PartB.nodeTime 28 := by
  have hpi : (ExactReplay.piI.lo : ℝ) ≤ Real.pi :=
    ExactReplay.piI_contains_pi.1
  have hp := theta_bounds.2
  unfold PartB.nodeTime PartB.nodeCoeff
  norm_num [ExactReplay.piI, ExactReplay.q] at hpi hp ⊢
  nlinarith

 theorem node36_lt_eta : PartB.nodeTime 36 < eta := by
  change PartB.nodeTime 36 < Real.pi / 2 - params.theta
  have h := theta_lt_node28
  unfold PartB.nodeTime PartB.nodeCoeff at h ⊢
  norm_num at h ⊢
  linarith

 theorem eta_lt_node37 : eta < PartB.nodeTime 37 := by
  change Real.pi / 2 - params.theta < PartB.nodeTime 37
  have h := node27_lt_theta
  unfold PartB.nodeTime PartB.nodeCoeff at h ⊢
  norm_num at h ⊢
  linarith

 theorem node62_lt_tau : PartB.nodeTime 62 < tau := by
  change PartB.nodeTime 62 < Real.pi / 2 - params.phi
  have h := phi_lt_node2
  unfold PartB.nodeTime PartB.nodeCoeff at h ⊢
  norm_num at h ⊢
  linarith

 theorem tau_lt_node63 : tau < PartB.nodeTime 63 := by
  change Real.pi / 2 - params.phi < PartB.nodeTime 63
  have h := node1_lt_phi
  unfold PartB.nodeTime PartB.nodeCoeff at h ⊢
  norm_num at h ⊢
  linarith

 theorem phase1_cell {i : PartB.Cell} {t : ℝ}
    (ht : t ∈ PartB.cellSet i) (hphase : t ≤ params.phi) : i.1 ≤ 1 := by
  by_contra hnot
  have hi : 2 ≤ i.1 := by omega
  have h2i : PartB.nodeTime 2 ≤ PartB.nodeTime i.1 :=
    PartB.nodeTime_mono hi
  linarith [phi_lt_node2, ht.1]

 theorem phase2_cell {i : PartB.Cell} {t : ℝ}
    (ht : t ∈ PartB.cellSet i)
    (hlo : params.phi < t) (hhi : t ≤ params.theta) :
    1 ≤ i.1 ∧ i.1 ≤ 27 := by
  constructor
  · by_contra hnot
    have hi : i.1 + 1 ≤ 1 := by omega
    have hend : PartB.nodeTime (i.1 + 1) ≤ PartB.nodeTime 1 :=
      PartB.nodeTime_mono hi
    linarith [node1_lt_phi, ht.2]
  · by_contra hnot
    have hi : 28 ≤ i.1 := by omega
    have h28i : PartB.nodeTime 28 ≤ PartB.nodeTime i.1 :=
      PartB.nodeTime_mono hi
    linarith [theta_lt_node28, ht.1]

 theorem phase3_cell {i : PartB.Cell} {t : ℝ}
    (ht : t ∈ PartB.cellSet i)
    (hlo : params.theta < t) (hhi : t ≤ eta) :
    27 ≤ i.1 ∧ i.1 ≤ 36 := by
  constructor
  · by_contra hnot
    have hi : i.1 + 1 ≤ 27 := by omega
    have hend : PartB.nodeTime (i.1 + 1) ≤ PartB.nodeTime 27 :=
      PartB.nodeTime_mono hi
    linarith [node27_lt_theta, ht.2]
  · by_contra hnot
    have hi : 37 ≤ i.1 := by omega
    have h37i : PartB.nodeTime 37 ≤ PartB.nodeTime i.1 :=
      PartB.nodeTime_mono hi
    linarith [eta_lt_node37, ht.1]

 theorem phase4_cell {i : PartB.Cell} {t : ℝ}
    (ht : t ∈ PartB.cellSet i)
    (hlo : eta < t) (hhi : t ≤ tau) :
    36 ≤ i.1 ∧ i.1 ≤ 62 := by
  constructor
  · by_contra hnot
    have hi : i.1 + 1 ≤ 36 := by omega
    have hend : PartB.nodeTime (i.1 + 1) ≤ PartB.nodeTime 36 :=
      PartB.nodeTime_mono hi
    linarith [node36_lt_eta, ht.2]
  · by_contra hnot
    have hi : 63 ≤ i.1 := by omega
    have h63i : PartB.nodeTime 63 ≤ PartB.nodeTime i.1 :=
      PartB.nodeTime_mono hi
    linarith [tau_lt_node63, ht.1]

 theorem phase5_cell {i : PartB.Cell} {t : ℝ}
    (ht : t ∈ PartB.cellSet i) (hlo : tau < t) : 62 ≤ i.1 := by
  by_contra hnot
  have hi : i.1 + 1 ≤ 62 := by omega
  have hend : PartB.nodeTime (i.1 + 1) ≤ PartB.nodeTime 62 :=
    PartB.nodeTime_mono hi
  linarith [node62_lt_tau, ht.2]

 theorem phi_nonneg : 0 ≤ params.phi :=
  (Romik.phi_pos_of_mem_box params_mem).le

 theorem tau_le_T : tau ≤ T := by
  unfold tau
  linarith [phi_nonneg]

 theorem zero_le_theta : 0 ≤ params.theta := by
  linarith [phi_nonneg, switchOrder.phi_le_theta]

 theorem eta_le_tau : eta ≤ tau := by
  simpa [eta, tau, T] using switchOrder.eta_le_tau

 theorem theta_le_eta : params.theta ≤ eta := by
  simpa [eta, T] using switchOrder.theta_le_eta

end Stage2
end PartC
end GerverSofa
