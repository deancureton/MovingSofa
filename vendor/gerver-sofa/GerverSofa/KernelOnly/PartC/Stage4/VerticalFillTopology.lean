import GerverSofa.KernelOnly.PartC.Stage4.NoHiddenContinuityFacts
import Mathlib.Topology.Connected.Basic

/-!
# Part C Stage 4: independent vertical-fill topology

This module isolates the connectedness half of the niche argument from the
upper-envelope/frontier equality.  It can therefore be kernel-built even while
the boundary module is still under repair.
-/

noncomputable section

namespace GerverSofa
namespace PartC
namespace Stage4

open Set

/-- Vertical fill below a parametrized graph. -/
def verticalFill (f : ℝ → Point) (I : Set ℝ) : Set Point :=
  {q | ∃ t ∈ I, q.1 = (f t).1 ∧ 0 ≤ q.2 ∧ q.2 < (f t).2}

/-- The three certified upper-envelope pieces as strict vertical fills. -/
def certifiedNicheRegion : Set Point :=
  verticalFill D (Icc (0 : ℝ) params.theta) ∪
  verticalFill (Romik.path params) (Icc params.phi tau) ∪
  verticalFill B (Icc eta T)

/-- Consecutive endpoint incidences of the three graph pieces. -/
theorem niche_piece_endpoints :
    B eta = Romik.path params params.phi ∧
    D params.theta = Romik.path params tau ∧
    (B T).2 = 0 ∧ (D 0).2 = 0 :=
  ⟨B_eta_eq_path_phi, D_theta_eq_path_tau,
    B_T_y_zero, D_zero_y_zero⟩

/-- A strict positive vertical fill is a continuous image of a connected
product. -/
theorem verticalFill_strict_isConnected
    {f : ℝ → Point} {I : Set ℝ}
    (hI : IsConnected I)
    (hf : ContinuousOn f I)
    (hy : ∀ t ∈ I, 0 < (f t).2) :
    IsConnected (verticalFill f I) := by
  let P : Set (ℝ × ℝ) := I ×ˢ Ico (0 : ℝ) 1
  have hP : IsConnected P := by
    dsimp [P]
    exact hI.prod (isConnected_Ico (by norm_num))
  let F : (ℝ × ℝ) → Point := fun z =>
    ((f z.1).1, z.2 * (f z.1).2)
  have hfcomp : ContinuousOn (fun z : ℝ × ℝ => f z.1) P := by
    exact hf.comp continuous_fst.continuousOn (by
      intro z hz
      exact hz.1)
  have hF : ContinuousOn F P := by
    dsimp [F]
    exact hfcomp.fst.prodMk (continuous_snd.continuousOn.mul hfcomp.snd)
  have himage : F '' P = verticalFill f I := by
    ext q
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hlt := mul_lt_mul_of_pos_right hz.2.2 (hy z.1 hz.1)
      exact ⟨z.1, hz.1, rfl,
        mul_nonneg hz.2.1 (hy z.1 hz.1).le, by simpa [F] using hlt⟩
    · rintro ⟨t, ht, hx, hy0, hylt⟩
      have htop := hy t ht
      let s : ℝ := q.2 / (f t).2
      have hs : s ∈ Ico (0 : ℝ) 1 := by
        constructor
        · exact div_nonneg hy0 htop.le
        · exact (div_lt_one htop).2 hylt
      refine ⟨(t, s), ⟨ht, hs⟩, ?_⟩
      apply Prod.ext
      · simpa [F] using hx.symm
      · dsimp [F, s]
        field_simp [ne_of_gt htop]
  rw [← himage]
  exact hP.image F hF

theorem D_fill_Icc_eq_Ioc :
    verticalFill D (Icc (0 : ℝ) params.theta) =
      verticalFill D (Ioc (0 : ℝ) params.theta) := by
  ext q
  constructor
  · rintro ⟨t, ht, hx, hy0, hylt⟩
    have htpos : 0 < t := by
      by_contra hnot
      have ht0 : t = 0 := le_antisymm (le_of_not_gt hnot) ht.1
      subst t
      rw [D_zero_y_zero] at hylt
      linarith
    exact ⟨t, ⟨htpos, ht.2⟩, hx, hy0, hylt⟩
  · rintro ⟨t, ht, hx, hy0, hylt⟩
    exact ⟨t, ⟨ht.1.le, ht.2⟩, hx, hy0, hylt⟩

theorem B_fill_Icc_eq_Ico :
    verticalFill B (Icc eta T) = verticalFill B (Ico eta T) := by
  ext q
  constructor
  · rintro ⟨t, ht, hx, hy0, hylt⟩
    have htlt : t < T := by
      by_contra hnot
      have htT : t = T := le_antisymm ht.2 (le_of_not_gt hnot)
      subst t
      rw [B_T_y_zero] at hylt
      linarith
    exact ⟨t, ⟨ht.1, htlt⟩, hx, hy0, hylt⟩
  · rintro ⟨t, ht, hx, hy0, hylt⟩
    exact ⟨t, ⟨ht.1, ht.2.le⟩, hx, hy0, hylt⟩

private theorem D_fill_connected :
    IsConnected (verticalFill D (Ioc (0 : ℝ) params.theta)) := by
  exact verticalFill_strict_isConnected
    (isConnected_Ioc theta_pos) D_continuous.continuousOn
    (by intro t ht; exact D_y_pos ht)

private theorem path_fill_connected :
    IsConnected
      (verticalFill (Romik.path params) (Icc params.phi tau)) := by
  exact verticalFill_strict_isConnected
    (isConnected_Icc (le_trans phi_lt_theta.le
      (le_trans theta_lt_eta.le eta_lt_tau.le)))
    pathContinuous.continuousOn (by
      intro t ht
      exact path_core_y_pos ht)

private theorem B_fill_connected :
    IsConnected (verticalFill B (Ico eta T)) := by
  exact verticalFill_strict_isConnected
    (isConnected_Ico eta_lt_T) B_continuous.continuousOn
    (by intro t ht; exact B_y_pos ht)

theorem niche_fills_overlap :
    (verticalFill D (Ioc (0 : ℝ) params.theta) ∩
      verticalFill (Romik.path params) (Icc params.phi tau)).Nonempty ∧
    (verticalFill (Romik.path params) (Icc params.phi tau) ∩
      verticalFill B (Ico eta T)).Nonempty := by
  refine ⟨?_, ?_⟩
  · let q : Point := ((D params.theta).1, (D params.theta).2 / 2)
    have hy0 : 0 ≤ q.2 := by
      dsimp [q]
      nlinarith [D_theta_y_pos]
    have hylt : q.2 < (D params.theta).2 := by
      dsimp [q]
      nlinarith [D_theta_y_pos]
    refine ⟨q, ?_, ?_⟩
    · exact ⟨params.theta, ⟨theta_pos, le_rfl⟩, rfl, hy0, hylt⟩
    · refine ⟨tau, ⟨?_, le_rfl⟩, ?_, ?_, ?_⟩
      · exact le_trans phi_lt_theta.le (le_trans theta_lt_eta.le eta_lt_tau.le)
      · dsimp [q]
        rw [← D_theta_eq_path_tau]
      · exact hy0
      · simpa [D_theta_eq_path_tau] using hylt
  · let q : Point := ((B eta).1, (B eta).2 / 2)
    have hy0 : 0 ≤ q.2 := by
      dsimp [q]
      nlinarith [B_eta_y_pos]
    have hylt : q.2 < (B eta).2 := by
      dsimp [q]
      nlinarith [B_eta_y_pos]
    refine ⟨q, ?_, ?_⟩
    · refine ⟨params.phi, ⟨le_rfl, ?_⟩, ?_, ?_, ?_⟩
      · exact le_trans phi_lt_theta.le (le_trans theta_lt_eta.le eta_lt_tau.le)
      · dsimp [q]
        rw [← B_eta_eq_path_phi]
      · exact hy0
      · simpa [B_eta_eq_path_phi] using hylt
    · exact ⟨eta, ⟨le_rfl, eta_lt_T⟩, rfl, hy0, hylt⟩

/-- Connectedness of the certified three-piece vertical-fill region. -/
theorem certifiedNicheRegion_connected : IsConnected certifiedNicheRegion := by
  unfold certifiedNicheRegion
  rw [D_fill_Icc_eq_Ioc, B_fill_Icc_eq_Ico]
  rcases niche_fills_overlap with ⟨hDX, hXB⟩
  have hDXc := D_fill_connected.union hDX path_fill_connected
  exact hDXc.union (by
    rcases hXB with ⟨q, hqX, hqB⟩
    exact ⟨q, Or.inr hqX, hqB⟩) B_fill_connected

end Stage4
end PartC
end GerverSofa
