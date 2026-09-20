import GerverSofa.KernelOnly.PartC.Stage4.NoHiddenMatchFacts

/-!
# Part C Stage 4: continuity of the matched velocity coefficients

This file turns the five exact coefficient matching statements into a public
continuity interface for `alphaBetaAt`, `alpha`, `beta`, `B`, and `D`.
-/

noncomputable section

namespace GerverSofa
namespace PartC
namespace Stage4

private theorem alphaBeta1_continuous :
    Continuous (Romik.alphaBeta1 params) := by
  unfold Romik.alphaBeta1
  fun_prop

private theorem alphaBeta2_continuous :
    Continuous (Romik.alphaBeta2 params) := by
  unfold Romik.alphaBeta2
  fun_prop

private theorem alphaBeta3_continuous :
    Continuous (Romik.alphaBeta3 params) := by
  unfold Romik.alphaBeta3
  fun_prop

private theorem alphaBeta4_continuous :
    Continuous (Romik.alphaBeta4 params) := by
  unfold Romik.alphaBeta4
  fun_prop

private theorem alphaBeta5_continuous :
    Continuous (Romik.alphaBeta5 params) := by
  unfold Romik.alphaBeta5
  fun_prop

/-- The literal nested-if velocity coefficient is continuous across all four
switches. -/
theorem alphaBetaAt_continuous : Continuous alphaBetaAt := by
  have h45 : Continuous
      (fun t : ℝ =>
        if t ≤ tau then Romik.alphaBeta4 params t
        else Romik.alphaBeta5 params t) := by
    exact alphaBeta4_continuous.if_le alphaBeta5_continuous
      continuous_id continuous_const (by
        intro t ht
        subst t
        exact alphaBeta_match45_direct)

  have h345 : Continuous
      (fun t : ℝ =>
        if t ≤ eta then Romik.alphaBeta3 params t
        else if t ≤ tau then Romik.alphaBeta4 params t
        else Romik.alphaBeta5 params t) := by
    exact alphaBeta3_continuous.if_le h45
      continuous_id continuous_const (by
        intro t ht
        subst t
        rw [if_pos eta_lt_tau.le]
        exact alphaBeta_match34_direct)

  have h2345 : Continuous
      (fun t : ℝ =>
        if t ≤ params.theta then Romik.alphaBeta2 params t
        else if t ≤ eta then Romik.alphaBeta3 params t
        else if t ≤ tau then Romik.alphaBeta4 params t
        else Romik.alphaBeta5 params t) := by
    exact alphaBeta2_continuous.if_le h345
      continuous_id continuous_const (by
        intro t ht
        subst t
        rw [if_pos theta_lt_eta.le]
        exact alphaBeta_match23_direct)

  have h12345 : Continuous
      (fun t : ℝ =>
        if t ≤ params.phi then Romik.alphaBeta1 params t
        else if t ≤ params.theta then Romik.alphaBeta2 params t
        else if t ≤ eta then Romik.alphaBeta3 params t
        else if t ≤ tau then Romik.alphaBeta4 params t
        else Romik.alphaBeta5 params t) := by
    exact alphaBeta1_continuous.if_le h2345
      continuous_id continuous_const (by
        intro t ht
        subst t
        rw [if_pos phi_lt_theta.le]
        exact alphaBeta_match12_direct)

  unfold alphaBetaAt
  exact h12345

theorem alpha_continuous : Continuous alpha := by
  unfold alpha
  exact continuous_fst.comp alphaBetaAt_continuous

theorem beta_continuous : Continuous beta := by
  unfold beta
  exact continuous_snd.comp alphaBetaAt_continuous

private theorem u_continuous : Continuous u := by
  unfold u
  fun_prop

private theorem v_continuous : Continuous v := by
  unfold v
  fun_prop

/-- Public continuity of the early reflected contact curve. -/
theorem D_continuous : Continuous D := by
  have hx := pathContinuous
  have hfirst := (continuous_fst.comp hx).sub
    (beta_continuous.mul (continuous_fst.comp u_continuous))
  have hsecond := (continuous_snd.comp hx).sub
    (beta_continuous.mul (continuous_snd.comp u_continuous))
  change Continuous (fun t : ℝ =>
    ((Romik.path params t).1 - beta t * (u t).1,
     (Romik.path params t).2 - beta t * (u t).2))
  exact hfirst.prodMk hsecond

/-- Public continuity of the late reflected contact curve. -/
theorem B_continuous : Continuous B := by
  have hx := pathContinuous
  have hfirst := (continuous_fst.comp hx).add
    (alpha_continuous.mul (continuous_fst.comp v_continuous))
  have hsecond := (continuous_snd.comp hx).add
    (alpha_continuous.mul (continuous_snd.comp v_continuous))
  change Continuous (fun t : ℝ =>
    ((Romik.path params t).1 + alpha t * (v t).1,
     (Romik.path params t).2 + alpha t * (v t).2))
  exact hfirst.prodMk hsecond

end Stage4
end PartC
end GerverSofa
