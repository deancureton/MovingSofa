import GerverSofa.KernelOnly.PartC.Stage4.SofaFiberTopology
import GerverSofa.KernelOnly.PartC.Stage4.NicheConnectedDirect

/-!
# Part C Stage 4: topology of the concrete fixed set

No new certificate structure is introduced here.  This file is intended to
close the two literal topology fields left by `RemainingTopologyTarget`.
-/

noncomputable section

namespace GerverSofa
namespace PartC
namespace Stage4

open Set

/-- The right endpoint of the niche roof still satisfies the zero-angle
horizontal support inequality of the cap. -/
private theorem B_T_fst_le_one : (B T).1 ≤ 1 := by
  have hBTK : B T ∈ K := B_mem_K ⟨eta_lt_T.le, le_rfl⟩
  rw [Romik.mem_K0] at hBTK
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) (Real.pi / 2) := by
    constructor
    · exact le_rfl
    · positivity
  have h := (hBTK.2 0 h0).1
  simpa [supportHalfU, dot, u, pathZero] using h

/-- The left endpoint of the zero-angle support face is the concrete anchor
and it is not removed by the niche. -/
theorem anchor_mem_direct : anchor ∈ G := by
  have hA0 : A 0 = anchor := Stage2.A_zero_eq_anchor
  have hK : anchor ∈ K := by
    rw [← hA0]
    exact Stage3.supportA_direct 0 (by
      constructor
      · norm_num
      · dsimp [T]; positivity)
  refine ⟨hK, ?_⟩
  intro hn
  rw [niche_eq_certifiedNicheRegion] at hn
  rcases hn with (hD | hx) | hB
  · rcases hD with ⟨t, ht, hx1, _hy0, _hylt⟩
    have htT : t < T := lt_of_le_of_lt ht.2 (lt_trans theta_lt_eta eta_lt_T)
    have htPhysical : t ∈ Icc (0 : ℝ) T := ⟨ht.1, htT.le⟩
    have hroof := nicheTopArc_fst_strictMono htPhysical
      (right_mem_Icc.2 (show (0 : ℝ) ≤ T by dsimp [T]; positivity)) htT
    have hleft : nicheTopArc t = D t := by
      simp [nicheTopArc, ht.2]
    change (nicheTopArc t).1 < (nicheTopArc T).1 at hroof
    rw [hleft, nicheTopArc_T] at hroof
    change (1 : ℝ) = (D t).1 at hx1
    linarith [B_T_fst_le_one]
  · rcases hx with ⟨t, ht, hx1, _hy0, _hylt⟩
    have hpath : (Romik.path params t).1 ≤
        (Romik.path params params.phi).1 :=
      core_path_fst_strictAnti.antitoneOn
        (left_mem_Icc.2 (lt_trans phi_lt_theta
          (lt_trans theta_lt_eta eta_lt_tau)).le)
        ht ht.1
    have hlate : (B eta).1 < (B T).1 :=
      B_fst_strictMono (left_mem_Icc.2 eta_lt_T.le)
        (right_mem_Icc.2 eta_lt_T.le) eta_lt_T
    have hroof : (Romik.path params t).1 < (B T).1 := by
      calc
        (Romik.path params t).1 ≤
            (Romik.path params params.phi).1 := hpath
        _ = (B eta).1 := congrArg Prod.fst B_eta_eq_path_phi.symm
        _ < (B T).1 := hlate
    change (1 : ℝ) = (Romik.path params t).1 at hx1
    linarith [B_T_fst_le_one]
  · rcases hB with ⟨t, ht, hx1, _hy0, _hylt⟩
    by_cases hT : t = T
    · subst t
      change (0 : ℝ) < (B T).2 at _hylt
      rw [B_T_y_zero] at _hylt
      exact (lt_irrefl 0 _hylt)
    · have htT : t < T := lt_of_le_of_ne ht.2 hT
      have hroof : (B t).1 < (B T).1 :=
        B_fst_strictMono ht (right_mem_Icc.2 eta_lt_T.le) htT
      change (1 : ℝ) = (B t).1 at hx1
      linarith [B_T_fst_le_one]

/-- Direct connectedness of the cap-minus-niche set, obtained from the
compact connected horizontal projection and the connected vertical fibres. -/
theorem G_connected_direct : IsConnected G :=
  G_connected_by_vertical_fibers

end Stage4
end PartC
end GerverSofa
